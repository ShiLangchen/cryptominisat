/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "propengine.h"
#include <cassert>
#include <cmath>
#include <optional>
#include <string.h>
#include <algorithm>
#include <limits.h>
#include <type_traits>
#include <vector>
#include <iomanip>
#include <set>
#include <algorithm>

#include "constants.h"
#include "eq.h"
#include "eqwatch.h"
#include "solver.h"
#include "clauseallocator.h"
#include "clause.h"
#include "solvertypesmini.h"
#include "time_mem.h"
#include "varupdatehelper.h"
#include "watchalgos.h"
#include "sqlstats.h"
#include "gaussian.h"

using namespace CMSat;
using std::cout;
using std::endl;
using std::set;

//#define DEBUG_ENQUEUE_LEVEL0
//#define VERBOSE_DEBUG_POLARITIES
//#define DEBUG_DYNAMIC_RESTART
// Uncomment the line below to enable ANF propagation debugging output
// #define DEBUG_ANF_PROP

/**
@brief Sets a sane default config and allocates handler classes
*/
PropEngine::PropEngine(const SolverConf *_conf, Solver *_solver, std::atomic<bool> *_must_interrupt_inter)
    : CNF(_conf, _must_interrupt_inter), order_heap_vsids(VarOrderLt(var_act_vsids)), qhead(0), solver(_solver)
{
}

PropEngine::~PropEngine() {}

void PropEngine::new_var(const bool bva, uint32_t orig_outer, const bool insert_varorder)
{
    CNF::new_var(bva, orig_outer, insert_varorder);

    var_act_vsids.insert(var_act_vsids.end(), 1, 0);
    vmtf_btab.insert(vmtf_btab.end(), 1, 0);
    vmtf_links.insert(vmtf_links.end(), 1, Link());
    xor_occurs_by_var.emplace_back();
    xor_count.emplace_back(0);
}

void PropEngine::new_vars(size_t n)
{
    CNF::new_vars(n);

    var_act_vsids.insert(var_act_vsids.end(), n, 0);
    vmtf_btab.insert(vmtf_btab.end(), n, 0);
    vmtf_links.insert(vmtf_links.end(), n, Link());
    xor_occurs_by_var.insert(xor_occurs_by_var.end(), n, vector<uint32_t>());
    xor_count.insert(xor_count.end(), n, 0);
}

void PropEngine::save_on_var_memory()
{
    CNF::save_on_var_memory();

    var_act_vsids.resize(nVars());
    var_act_vsids.shrink_to_fit();
}

/**
 @ *brief Attach normal a clause to the watchlists

 Handles 2, 3 and >3 clause sizes differently and specially
 */

void PropEngine::attachClause(const Clause &c, const bool checkAttach)
{
    const ClOffset offset = cl_alloc.get_offset(&c);

    assert(c.size() > 2);
    if (checkAttach) {
        assert(value(c[0]) == l_Undef);
        assert(value(c[1]) == l_Undef || value(c[1]) == l_False);
    }

#ifdef DEBUG_ATTACH
    for (uint32_t i = 0; i < c.size(); i++) {
        assert(varData[c[i].var()].removed == Removed::none);
    }
#endif //DEBUG_ATTACH

    const Lit blocked_lit = c[2];
    watches[c[0]].push(Watched(offset, blocked_lit));
    watches[c[1]].push(Watched(offset, blocked_lit));
}

void PropEngine::attach_xor_clause(uint32_t at)
{
    Xor &x = xorclauses[at];
    assert(x.size() > 2);
    DEBUG_ATTACH_MORE_DO(for (const auto &v : x) assert(varData[v].removed == Removed::none));

    assert(value(x[0]) == l_Undef);
    assert(value(x[1]) == l_Undef);
    auto w = GaussWatched::plain_xor(at);
    gwatches[x[0]].push(w);
    gwatches[x[1]].push(w);
    x.watched[0] = 0;
    x.watched[1] = 1;
    
    // Track occurrences for alias-update refresh
    for (uint32_t v : x) {
        if (v >= xor_occurs_by_var.size()) {
            xor_occurs_by_var.resize(v + 1);
        }
        xor_occurs_by_var[v].push_back(at);
    }

    // ANF-Elim: Initialize active_resolved_vars (variables with odd count after alias resolution)
    update_xor_active_vars(at);
}

void PropEngine::update_xor_active_vars(uint32_t at)
{
    Xor &x = xorclauses[at];
    x.active_resolved_vars.clear();

    // Ensure scratch space is large enough
    if (xor_count.size() < nVars()) {
        xor_count.resize(nVars(), 0);
    }

    // Parity count using flat array; remember touched vars to reset later
    for (uint32_t i = 0; i < x.size(); i++) {
        uint32_t orig_var = x[i];
        Lit resolved_lit = resolve_alias(Lit(orig_var, false));
        uint32_t v = resolved_lit.var();

        if (xor_count[v] == 0) xor_touched.push_back(v);
        xor_count[v] ^= 1; // toggle parity
    }

    // Collect vars with odd parity
    for (uint32_t v : xor_touched) {
        if (xor_count[v] & 1) x.active_resolved_vars.push_back(v);
        xor_count[v] = 0;
    }
    xor_touched.clear();

    // Keep active vars sorted for binary_search membership checks
    std::sort(x.active_resolved_vars.begin(), x.active_resolved_vars.end());
    
#ifdef DEBUG_ANF_PROP
    cout << "[ANF-PROP] Updated active_resolved_vars for XOR clause #" << at << ": ";
    cout << "Original vars: ";
    for (uint32_t i = 0; i < x.size(); i++) {
        uint32_t orig_var = x[i];
        Lit orig_lit = Lit(orig_var, false);
        Lit resolved_lit = resolve_alias(orig_lit);
        cout << orig_var + 1;
        if (resolved_lit.var() != orig_var) {
            cout << "->" << resolved_lit.var() + 1;
        }
        if (i + 1 < x.size()) cout << " ";
    }
    cout << " | Active vars (odd count): ";
    for (uint32_t v : x.active_resolved_vars) {
        cout << v + 1 << " ";
    }
    cout << "| RHS=" << x.rhs << endl;
#endif
}

void PropEngine::update_xor_active_vars_for_var(uint32_t var)
{
    // CRITICAL FIX: Update all XOR clauses that contain this variable (or its alias)
    // We need to check gwatches to find all XOR clauses containing this variable
    // Also need to check all XOR clauses to see if they contain this variable after alias resolution
    if (gwatches.size() <= var) return;
    
    vec<GaussWatched> &ws = gwatches[var];
    std::set<uint32_t> updated_xors;  // Avoid updating the same XOR clause multiple times
    
    // First, update XOR clauses that have this variable in their watch list
    for (const GaussWatched &w : ws) {
        if (w.matrix_num == 1000) {
            uint32_t at = w.row_n;
            if (updated_xors.find(at) == updated_xors.end()) {
                update_xor_active_vars(at);
                updated_xors.insert(at);
            }
        }
    }

    // Next, update XOR clauses where this original variable occurs
    if (var < xor_occurs_by_var.size()) {
        for (uint32_t at : xor_occurs_by_var[var]) {
            if (updated_xors.find(at) != updated_xors.end()) continue;
            update_xor_active_vars(at);
            updated_xors.insert(at);
        }
    }
}

void PropEngine::attach_eq_clause(uint32_t at)
{
    Eq &e = eq_clauses[at];
    const auto &lits = e.get_lits();
    assert(lits.size() >= 2);

    assert(value(e[0]) == l_Undef);
    assert(value(e[1]) == l_Undef);

    eq_watches[e[0].var()].push(EqWatched(at));
    eq_watches[e[1].var()].push(EqWatched(at));
    e.watched[0] = 0;
    e.watched[1] = 1;

    aux_to_eid[e.get_aux_lit().var()] = e.get_eid();
}

/**
@brief Detaches a (potentially) modified clause

The first two literals might have chaned through modification, so they are
passed along as arguments -- they are needed to find the correct place where
the clause is
*/
void PropEngine::detach_modified_clause(const Lit lit1, const Lit lit2, const Clause *address)
{
    ClOffset offset = cl_alloc.get_offset(address);
    removeWCl(watches[lit1], offset);
    removeWCl(watches[lit2], offset);
}

PropBy PropEngine::gauss_jordan_elim(const Lit p, const uint32_t currLevel)
{
    VERBOSE_PRINT("PropEngine::gauss_jordan_elim called, declev: " << decisionLevel() << " lit to prop: " << p);
    const uint32_t pv = p.var();

    if (gmatrices.empty() && xorclauses.empty()) return PropBy();

    // reset gqueuedata and update set vars in gmatrices
    for (uint32_t i = 0; i < gqueuedata.size(); i++) {
        if (gqueuedata[i].disabled || !gmatrices[i]->is_initialized()) continue;
        gqueuedata[i].reset();
        gmatrices[i]->update_cols_vals_set();
    }

    bool confl_in_gauss = false;
    assert(gwatches.size() > pv);
    vec<GaussWatched> &ws = gwatches[pv];
    GaussWatched *i = ws.begin();
    GaussWatched *j = i;
    const GaussWatched *end = ws.end();

    PropBy confl;
    for (; i != end; i++) {
        if (i->matrix_num == 1000) {
            const uint32_t at = i->row_n;
            auto &x = xorclauses[at];
            
            // ANF-Elim: Update active_resolved_vars before processing to ensure it's current
            // This is critical because alias changes may have occurred since last update
            update_xor_active_vars(at);
            
            bool which; // which watch is this
            SLOW_DEBUG_DO(assert(!x.trivial()));
            SLOW_DEBUG_DO(assert(x.watched[0] < x.size()));
            SLOW_DEBUG_DO(assert(x.watched[1] < x.size()));
            
            // CRITICAL FIX: Check resolved variables, not original variables
            // When alias changes, the original variable at watched position may be aliased
            uint32_t watched0_orig = x[x.watched[0]];
            uint32_t watched1_orig = x[x.watched[1]];
            Lit watched0_lit = Lit(watched0_orig, false);
            Lit watched1_lit = Lit(watched1_orig, false);
            Lit watched0_resolved = resolve_alias(watched0_lit);
            Lit watched1_resolved = resolve_alias(watched1_lit);
            uint32_t watched0_resolved_var = watched0_resolved.var();
            uint32_t watched1_resolved_var = watched1_resolved.var();
            
            if (pv == watched0_resolved_var) {
                which = 0;
            } else {
                which = 1;
                if (watched1_resolved_var != pv) {
                    cout << "ERROR. Going through pv: " << pv + 1 << " xor: " << x << endl;
                    cout << "  watched[0] orig=" << watched0_orig + 1 << ", resolved=" << watched0_resolved_var + 1 << endl;
                    cout << "  watched[1] orig=" << watched1_orig + 1 << ", resolved=" << watched1_resolved_var + 1 << endl;
                }
                assert(watched1_resolved_var == pv);
            }

            // ANF-Elim: Use bitset (active_resolved_vars) and watched literals
            // active_resolved_vars contains variables (after alias resolution) that appear odd times
            // Only these variables contribute to XOR parity (x⊕x=0 elimination already applied)
            
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-PROP] Processing XOR clause #" << at << " triggered by var " << pv + 1 << " (watch " << (which ? 1 : 0) << ")" << endl;
            cout << "  Original XOR: ";
            for (uint32_t i2 = 0; i2 < x.size(); i2++) {
                uint32_t orig_var = x[i2];
                Lit orig_lit = Lit(orig_var, false);
                Lit resolved_lit = resolve_alias(orig_lit);
                cout << orig_var + 1;
                if (resolved_lit.var() != orig_var) {
                    cout << "->" << resolved_lit.var() + 1;
                }
                if (i2 + 1 < x.size()) cout << " ⊕ ";
            }
            cout << " = " << x.rhs << endl;
            cout << "  Active resolved vars: ";
            for (uint32_t v : x.active_resolved_vars) {
                cout << v + 1 << " ";
            }
            cout << endl;
#endif
            
            // Compute parity using only active_resolved_vars
            uint32_t unknown = 0;
            uint32_t unknown_at = 0;
            uint32_t unknown_at_var = 0;  // resolved variable for propagation
            bool rhs = false;
            
            // Iterate through active_resolved_vars (variables that contribute to parity)
            for (uint32_t resolved_var : x.active_resolved_vars) {
                if (value(resolved_var) == l_Undef) {
                    unknown++;
                    // Find the original position in XOR clause for this resolved variable
                    // We need to find a position where the original variable resolves to resolved_var
                    bool found = false;
                    for (uint32_t i2 = 0; i2 < x.size(); i2++) {
                        uint32_t orig_var = x[i2];
                        Lit orig_lit = Lit(orig_var, false);
                        Lit resolved_lit = resolve_alias(orig_lit);
                        if (resolved_lit.var() == resolved_var) {
                            unknown_at = i2;
                            unknown_at_var = resolved_var;
                            found = true;
                            
                            // Check if this can be a new watch
                            if (i2 != x.watched[!which]) {
                                // it's not the other watch. So we can update current watch to this
                                // CRITICAL FIX: Update watched position and ensure watch is registered for original variable
                                // Note: gwatches is indexed by original variables, not resolved variables
                                // This ensures that when the original variable is assigned, the XOR clause is triggered
                                uint32_t old_watched_orig = x[x.watched[which]];
                                
                                // Remove old watch if the old watched variable is still valid
                                // (In practice, the watch list is cleaned lazily, so we just update the position)
                                x.watched[which] = i2;
                                
                                // Add watch for the new original variable
                                // This ensures the XOR clause is triggered when this variable is assigned
                                gwatches[orig_var].push(GaussWatched::plain_xor(at));
                                
#ifdef DEBUG_ANF_PROP
                                cout << "  Found new watch at position " << i2 << " (orig var " << orig_var + 1 
                                     << ", resolved to " << resolved_var + 1 << ")" << endl;
                                cout << "    Old watched orig var: " << old_watched_orig + 1 << endl;
#endif
                                goto next;
                            }
                            break;  // Found the position, no need to continue
                        }
                    }
                    if (!found) {
                        // This shouldn't happen, but handle gracefully
                        // Update active_resolved_vars and retry
#ifdef DEBUG_ANF_PROP
                        cout << "  WARNING: Could not find original position for resolved var " << resolved_var + 1 << ", updating bitset..." << endl;
#endif
                        update_xor_active_vars(at);
                        goto next;
                    }
                } else {
                    bool var_val = (value(resolved_var) == l_True);
                    rhs ^= var_val;
#ifdef DEBUG_ANF_PROP
                    cout << "  Resolved var " << resolved_var + 1 << " = " << var_val << " (contributes to RHS: " << rhs << ")" << endl;
#endif
                }
            }
            
            assert(unknown < 2);
            if (unknown == 1) {
                // this is the OTHER watch for sure
                // CRITICAL FIX: Verify that unknown_at matches the other watch position
                // But note: we check by resolved variable, so the position should still match
                // (The watched positions track original variable positions, which should still be correct)
                if (unknown_at != x.watched[!which]) {
                    // This can happen if alias changed the resolved variable but not the position
                    // In this case, we need to update the watched position
#ifdef DEBUG_ANF_PROP
                    cout << "  WARNING: unknown_at (" << unknown_at << ") != watched[!which] (" 
                         << x.watched[!which] << "), updating watch position" << endl;
#endif
                    // Find the correct position for the other watch
                    uint32_t other_watched_orig = x[x.watched[!which]];
                    Lit other_watched_lit = Lit(other_watched_orig, false);
                    Lit other_watched_resolved = resolve_alias(other_watched_lit);
                    if (other_watched_resolved.var() != unknown_at_var) {
                        // The other watch's resolved variable doesn't match, update it
                        x.watched[!which] = unknown_at;
                        // Also need to update gwatches for the new position
                        uint32_t new_orig_var = x[unknown_at];
                        gwatches[new_orig_var].push(GaussWatched::plain_xor(at));
                    }
                }
                x.prop_confl_watch = !which;
                
                // CRITICAL: Collect used_factors at propagation time (not during conflict analysis)
                // This ensures we use the alias state that existed at propagation time, not later
                x.last_used_factors.clear();
                x.prop_level = decisionLevel();
                x.prop_sublevel = trail.size();
                
                // Collect enabling factors for all aliases used in this XOR clause
                for (uint32_t i2 = 0; i2 < x.size(); i2++) {
                    uint32_t orig_var = x[i2];
                    if (!is_aux_var(orig_var)) continue;
                    
                    Lit orig_lit = Lit(orig_var, false);
                    Lit resolved_lit = resolve_alias(orig_lit);
                    
                    if (resolved_lit.var() != orig_var) {
                        // This aux variable was aliased, collect its enabling factors
                        auto it = aux_to_eid.find(orig_var);
                        if (it != aux_to_eid.end()) {
                            const Eq &eq = eq_clauses[it->second];
                            
                            // Collect all factors that are True (these enable the alias)
                            for (uint32_t k = 0; k < eq.size(); k++) {
                                const Lit &factor = eq[k];
                                if (value(factor) == l_True) {
                                    // Store canonicalized factor (resolved)
                                    Lit canonical_factor = resolve_alias(factor);
                                    x.last_used_factors.push_back(canonical_factor);
                                }
                            }
                        }
                    }
                }
                
                // CRITICAL FIX: Use resolved variable for propagation (if alias was applied)
                // Ensure the propagated variable is indeed unassigned and in active_resolved_vars
                assert(value(unknown_at_var) == l_Undef && "Propagated variable must be unassigned");
            assert(std::binary_search(x.active_resolved_vars.begin(), x.active_resolved_vars.end(), unknown_at_var)
                   && "Propagated variable must be in active_resolved_vars");
                Lit prop_lit = Lit(unknown_at_var, rhs == x.rhs);
#ifdef DEBUG_ANF_PROP
                cout << "  -> PROPAGATE: unknown=" << unknown << " (var " << unknown_at_var + 1 << " at pos " << unknown_at << "), computed RHS=" << rhs << ", clause RHS=" << x.rhs << ", propagate " << prop_lit << " at level " << decisionLevel() << endl;
                cout << "  -> Recorded " << x.last_used_factors.size() << " used factors at propagation time" << endl;
#endif
                enqueue<false>(prop_lit, decisionLevel(), PropBy(1000, at));
                *j++ = *i;
                goto next;
            }
            assert(unknown == 0);
            if (rhs != x.rhs) {
                x.prop_confl_watch = 2 + which;
                
                // CRITICAL: Collect used_factors at conflict time (not during conflict analysis)
                // This ensures we use the alias state that existed at conflict time, not later
                x.last_used_factors.clear();
                x.prop_level = decisionLevel();
                x.prop_sublevel = trail.size();
                
                // Collect enabling factors for all aliases used in this XOR clause
                for (uint32_t i2 = 0; i2 < x.size(); i2++) {
                    uint32_t orig_var = x[i2];
                    if (!is_aux_var(orig_var)) continue;
                    
                    Lit orig_lit = Lit(orig_var, false);
                    Lit resolved_lit = resolve_alias(orig_lit);
                    
                    if (resolved_lit.var() != orig_var) {
                        // This aux variable was aliased, collect its enabling factors
                        auto it = aux_to_eid.find(orig_var);
                        if (it != aux_to_eid.end()) {
                            const Eq &eq = eq_clauses[it->second];
                            
                            // Collect all factors that are True (these enable the alias)
                            for (uint32_t k = 0; k < eq.size(); k++) {
                                const Lit &factor = eq[k];
                                if (value(factor) == l_True) {
                                    // Store canonicalized factor (resolved)
                                    Lit canonical_factor = resolve_alias(factor);
                                    x.last_used_factors.push_back(canonical_factor);
                                }
                            }
                        }
                    }
                }
                
                confl = PropBy(1000, at);
#ifdef DEBUG_ANF_PROP
                cout << "  -> CONFLICT: computed RHS=" << rhs << ", clause RHS=" << x.rhs << ", conflict at level " << decisionLevel() << endl;
                cout << "  -> Recorded " << x.last_used_factors.size() << " used factors at conflict time" << endl;
#endif
                *j++ = *i;
                i++;
                break;
            } else {
#ifdef DEBUG_ANF_PROP
                cout << "  -> SATISFIED: computed RHS=" << rhs << ", clause RHS=" << x.rhs << endl;
#endif
                *j++ = *i;
            }
        } else {
            SLOW_DEBUG_DO(assert(i->matrix_num < gmatrices.size()));
            if (!gmatrices[i->matrix_num]->is_initialized()) continue; //remove watch and continue
            gqueuedata[i->matrix_num].new_resp_var = numeric_limits<uint32_t>::max();
            gqueuedata[i->matrix_num].new_resp_row = numeric_limits<uint32_t>::max();
            gqueuedata[i->matrix_num].do_eliminate = false;
            gqueuedata[i->matrix_num].currLevel = currLevel;

            if (gmatrices[i->matrix_num]->find_truths(i, j, pv, i->row_n, gqueuedata[i->matrix_num])) {
                continue;
            } else {
                confl_in_gauss = true;
                i++;
                break;
            }
        }
    next:;
    }

    for (; i != end; i++) *j++ = *i;
    ws.shrink(i - j);
    if (confl != PropBy()) return confl;

    for (size_t g = 0; g < gqueuedata.size(); g++) {
        if (gqueuedata[g].disabled || !gmatrices[g]->is_initialized()) continue;

        if (gqueuedata[g].do_eliminate) {
            gmatrices[g]->eliminate_col(pv, gqueuedata[g]);
            confl_in_gauss |= (gqueuedata[g].ret == gauss_res::confl);
        }
    }

    for (GaussQData &gqd: gqueuedata) {
        if (gqd.disabled) continue;

        //There was a conflict but this is not that matrix.
        //Just skip.
        if (confl_in_gauss && gqd.ret != gauss_res::confl) continue;

        switch (gqd.ret) {
            case gauss_res::confl: {
                gqd.num_conflicts++;
                qhead = trail.size();
                return gqd.confl;
            }

            case gauss_res::prop:
                gqd.num_props++;
                break;

            case gauss_res::none:
                //nothing
                break;

            default:
                assert(false);
                return PropBy();
        }
    }
    return PropBy();
}

void PropEngine::eq_elim(const Lit p)
{
    VERBOSE_PRINT("PropEngine::eq_elim called, declev: " << decisionLevel() << " lit to prop: " << p);

    const uint32_t pv = p.var();

    if (value(pv) == l_Undef) {
        if (!is_aux_var(pv)) {
            vec<EqWatched> &ws = eq_watches[pv];
            const EqWatched *end = ws.end();
            for (EqWatched *i = ws.begin(); i != end; i++) {
                const auto at = i->eid;
                auto &eq = eq_clauses[at];
                const Lit aux_lit = eq.get_aux_lit();
                const int aux_lit_int = aux_lit.toInt();

                bool which;
                if (eq[eq.watched[0]].var() == pv) {
                    which = 0;
                } else {
                    which = 1;
                    assert(eq[eq.watched[1]].var() == pv);
                }

                const Lit other = eq[eq.watched[!which]];
                std::optional<Lit> old_alias = alias[aux_lit_int];
                if (value(other) == l_Undef) {
                    alias[aux_lit_int] = std::nullopt;
                } else { // value(other) != l_Undef
                    if (value(aux_lit) == l_Undef && value(other) == l_True) {
                        alias[aux_lit_int] = eq[eq.watched[which]];
                    }
                }
                // ANF-Elim: If alias changed, update XOR clauses
                if (alias[aux_lit_int] != old_alias) {
#ifdef DEBUG_ANF_PROP
                    cout << "[ANF-PROP] Alias changed for aux var " << aux_lit.var() + 1 << " (Eq clause #" << at << "): ";
                    if (old_alias.has_value()) {
                        cout << old_alias.value();
                    } else {
                        cout << "none";
                    }
                    cout << " -> ";
                    if (alias[aux_lit_int].has_value()) {
                        cout << alias[aux_lit_int].value();
                    } else {
                        cout << "none";
                    }
                    cout << " at level " << decisionLevel() << endl;
#endif
                    update_xor_active_vars_for_var(aux_lit.var());
                    if (old_alias.has_value()) {
                        update_xor_active_vars_for_var(old_alias.value().var());
                    }
                    if (alias[aux_lit_int].has_value()) {
                        update_xor_active_vars_for_var(alias[aux_lit_int].value().var());
                    }
                }
            }
        } else {
            auto &eq = eq_clauses[aux_to_eid[pv]];
            assert(eq.get_eid() == aux_to_eid[pv]);
            const int aux_lit_int = eq.get_aux_lit().toInt();
            std::optional<Lit> old_alias = alias[aux_lit_int];
            if (value(eq[eq.watched[0]]) == l_Undef && value(eq[eq.watched[1]]) == l_Undef) {
                alias[aux_lit_int] = std::nullopt;
            } else if (value(eq[eq.watched[0]]) == l_Undef && value(eq[eq.watched[1]]) == l_True) {
                alias[aux_lit_int] = eq[eq.watched[0]];
            } else if (value(eq[eq.watched[1]]) == l_Undef && value(eq[eq.watched[0]]) == l_True) {
                alias[aux_lit_int] = eq[eq.watched[1]];
            } else {
                assert(alias[aux_lit_int] == std::nullopt);
            }
            // ANF-Elim: If alias changed, update XOR clauses
            if (alias[aux_lit_int] != old_alias) {
#ifdef DEBUG_ANF_PROP
                cout << "[ANF-PROP] Alias changed for aux var " << eq.get_aux_lit().var() + 1 << " (Eq clause #" << aux_to_eid[pv] << "): ";
                if (old_alias.has_value()) {
                    cout << old_alias.value();
                } else {
                    cout << "none";
                }
                cout << " -> ";
                if (alias[aux_lit_int].has_value()) {
                    cout << alias[aux_lit_int].value();
                } else {
                    cout << "none";
                }
                cout << " at level " << decisionLevel() << endl;
#endif
                update_xor_active_vars_for_var(eq.get_aux_lit().var());
                if (old_alias.has_value()) {
                    update_xor_active_vars_for_var(old_alias.value().var());
                }
                if (alias[aux_lit_int].has_value()) {
                    update_xor_active_vars_for_var(alias[aux_lit_int].value().var());
                }
            }
        }
        return;
    }

    if (is_aux_var(pv)) {
        const auto &eq = eq_clauses[aux_to_eid[pv]];
        const int aux_lit_int = eq.get_aux_lit().toInt();
        std::optional<Lit> old_alias = alias[aux_lit_int];
        alias[aux_lit_int] = std::nullopt;
        // ANF-Elim: If alias changed, update XOR clauses
        if (alias[aux_lit_int] != old_alias) {
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-PROP] Alias changed for aux var " << pv + 1 << " (Eq clause #" << aux_to_eid[pv] << "): ";
            if (old_alias.has_value()) {
                cout << old_alias.value();
            } else {
                cout << "none";
            }
            cout << " -> none at level " << decisionLevel() << endl;
#endif
            update_xor_active_vars_for_var(pv);
            if (old_alias.has_value()) {
                update_xor_active_vars_for_var(old_alias.value().var());
            }
        }
        return;
    }

    vec<EqWatched> &ws = eq_watches[pv];
    EqWatched *i = ws.begin();
    EqWatched *j = i;
    const EqWatched *end = ws.end();

    for (; i != end; i++) {
        auto at = i->eid;
        auto &eq = eq_clauses[at];

        bool which;
        if (eq[eq.watched[0]].var() == pv) {
            which = 0;
        } else {
            which = 1;
            assert(eq[eq.watched[1]].var() == pv);
        }

        const Lit the_other_watched = eq[eq.watched[!which]];
        const Lit aux_lit = eq.get_aux_lit();
        const int aux_lit_int = aux_lit.toInt();

        std::optional<Lit> old_alias = alias[aux_lit_int];
        if (value(eq[eq.watched[which]]) == l_False) {
            alias[aux_lit_int] = std::nullopt;
            // ANF-Elim: If alias changed, update XOR clauses
            if (alias[aux_lit_int] != old_alias) {
#ifdef DEBUG_ANF_PROP
                cout << "[ANF-PROP] Alias changed for aux var " << aux_lit.var() + 1 << " (Eq clause #" << at << "): ";
                if (old_alias.has_value()) {
                    cout << old_alias.value();
                } else {
                    cout << "none";
                }
                cout << " -> none at level " << decisionLevel() << endl;
#endif
                update_xor_active_vars_for_var(aux_lit.var());
                if (old_alias.has_value()) {
                    update_xor_active_vars_for_var(old_alias.value().var());
                }
            }
            *j++ = *i;
            goto next;
        }

        if (value(the_other_watched) == l_False) {
            // no need to do some replace,
            assert(alias[aux_lit_int] == std::nullopt);
            *j++ = *i;
            goto next;
        }

        for (uint32_t i2 = 0; i2 < eq.size(); i2++) {
            if (i2 == eq.watched[0] || i2 == eq.watched[1]) {
                continue;
            }
            const Lit &l2 = eq[i2];
            if (value(l2) != l_True) {
                eq.watched[which] = i2;
                eq_watches[l2.var()].push(EqWatched(at));
                goto next;
            }
        }

        // now, all the literals except the_other_watched are TRUE
        // if the_other_watched and aux_lit are both UNDEF, they are eq.
        old_alias = alias[aux_lit_int];
        if (value(the_other_watched) == l_Undef && value(aux_lit) == l_Undef) {
            alias[aux_lit_int] = the_other_watched;
        } else {
            alias[aux_lit_int] = std::nullopt;
        }
        // ANF-Elim: If alias changed, update XOR clauses
        if (alias[aux_lit_int] != old_alias) {
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-PROP] Alias changed for aux var " << aux_lit.var() + 1 << " (Eq clause #" << at << "): ";
            if (old_alias.has_value()) {
                cout << old_alias.value();
            } else {
                cout << "none";
            }
            cout << " -> ";
            if (alias[aux_lit_int].has_value()) {
                cout << alias[aux_lit_int].value();
            } else {
                cout << "none";
            }
            cout << " at level " << decisionLevel() << endl;
#endif
            update_xor_active_vars_for_var(aux_lit.var());
            if (old_alias.has_value()) {
                update_xor_active_vars_for_var(old_alias.value().var());
            }
            if (alias[aux_lit_int].has_value()) {
                update_xor_active_vars_for_var(alias[aux_lit_int].value().var());
            }
        }
        *j++ = *i;

    next:;
    }
    for (; i != end; i++) *j++ = *i;
    ws.shrink(i - j);
}

lbool PropEngine::bnn_prop(const uint32_t bnn_idx, uint32_t level, Lit /*l*/, BNNPropType prop_t)
{
    BNN *bnn = bnns[bnn_idx];
    switch (prop_t) {
        case bnn_neg_t:
            bnn->ts++;
            bnn->undefs--;
            break;
        case bnn_pos_t:
            bnn->undefs--;
            break;
        case bnn_out_t:
            break;
    }
#ifdef SLOW_DEBUG
    assert(bnn->ts >= 0);
    assert(bnn->undefs >= 0);
    assert(bnn->ts <= (int32_t)bnn->size());
    assert(bnn->undefs <= (int32_t)bnn->size());
#endif

    const int32_t ts = bnn->ts;
    const int32_t undefs = bnn->undefs;

    if (ts + undefs < bnn->cutoff) {
        // we are under the cutoff no matter what undef+unknowns is
        if (bnn->set) {
            //                 cout << "returning l_False from bnn_prop" <<  "declev: " << decisionLevel() << endl;
            return l_False;
        }

        if (value(bnn->out) == l_False) return l_True;
        if (value(bnn->out) == l_True) return l_False;

        assert(value(bnn->out) == l_Undef);
        enqueue<false>(~bnn->out, level, PropBy(bnn_idx, nullptr));
        //         cout << "BNN prop set BNN out " << ~bnn->out << " due to being under for sure" << endl;
        return l_True;
    }

    if (ts >= bnn->cutoff) {
        // we are over the cutoff
        if (bnn->set) {
            return l_True;
        }

        // we are at the cutoff no matter what undefs is
        if (value(bnn->out) == l_True) return l_True;
        if (value(bnn->out) == l_False) return l_False;

        assert(value(bnn->out) == l_Undef);
        enqueue<false>(bnn->out, level, PropBy(bnn_idx, nullptr));
        //         cout << "BNN prop set BNN out " << bnn->out << " due to being over for sure" << endl;        }
        return l_True;
    }

    if (((!bnn->set && value(bnn->out) == l_True) || bnn->set) && bnn->cutoff - ts == undefs) {
        //it's TRUE and UNDEF is exactly what's missing

        for (const auto &p: *bnn) {
            if (value(p) == l_Undef) {
                enqueue<false>(p, level, PropBy(bnn_idx, nullptr));
            }
        }
        return l_True;
    }

    if (((!bnn->set && value(bnn->out) == l_False) && bnn->cutoff == ts + 1)) {
        //it's FALSE and UNDEF must ALL be set to 0

        for (const auto &p: *bnn) {
            if (value(p) == l_Undef) {
                enqueue<false>(~p, level, PropBy(bnn_idx, nullptr));
            }
        }
        return l_True;
    }

    return l_Undef;
}

vector<Lit> *PropEngine::get_bnn_reason(BNN *bnn, Lit lit)
{
    //     cout << "Getting BNN reason, lit: " << lit << " bnn: " << *bnn << endl;
    //     cout << "values: ";
    //     for(const auto& l: bnn->in) {
    //         cout << l << " val: " << value(l) << " , ";
    //     }
    //     if (!bnn->set) {
    //         cout << " -- out : " << value(bnn->out);
    //     }
    //     cout << endl;

    if (lit == lit_Undef) {
        get_bnn_confl_reason(bnn, &bnn_confl_reason);
        return &bnn_confl_reason;
    }

    auto &reason = varData[lit.var()].reason;
    //     cout
    //     << " reason lev: " << varData[lit.var()].level
    //     << " sublev: " << varData[lit.var()].sublevel
    //     << " reason type: " << varData[lit.var()].reason.getType()
    //     << endl;
    assert(reason.isBNN());
    if (reason.bnn_reason_set()) {
        return &bnn_reasons[reason.get_bnn_reason()];
    }

    vector<Lit> *ret;

    //Get an empty slot
    uint32_t empty_slot;
    if (bnn_reasons_empty_slots.empty()) {
        bnn_reasons.push_back(vector<Lit>());
        empty_slot = bnn_reasons.size() - 1;
    } else {
        empty_slot = bnn_reasons_empty_slots.back();
        bnn_reasons_empty_slots.pop_back();
    }
    ret = &bnn_reasons[empty_slot];
    reason.set_bnn_reason(empty_slot);

    get_bnn_prop_reason(bnn, lit, ret);
    //     cout << "get_bnn_reason (" << lit << ") returning: ";
    //     for(const auto& l: *ret) {
    //         cout << l << " val(" << value(l) << ") ";
    //     }
    //     cout << "0" << endl;

    return ret;
}

void PropEngine::get_bnn_confl_reason(BNN *bnn, vector<Lit> *ret)
{
    assert(bnn->set || value(bnn->out) != l_Undef);

    //It's set to TRUE, but it's actually LESS than cutoff
    if (bnn->set || (!bnn->set && value(bnn->out) == l_True)) {
        ret->clear();
        if (!bnn->set) ret->push_back(~bnn->out);

        int32_t need = bnn->size() - bnn->cutoff + 1;
        for (const auto &l: *bnn) {
            if (value(l) == l_False) {
                ret->push_back(l);
                need--;
            }
            if (need == 0) break;
        }
    }

    //it's set to FALSE but it's actually MORE than cutoff.
    if ((!bnn->set && value(bnn->out) == l_False)) {
        ret->clear();
        if (!bnn->set) ret->push_back(bnn->out);

        int32_t need = bnn->cutoff;
        for (const auto &l: *bnn) {
            if (value(l) == l_True) {
                ret->push_back(~l);
                need--;
            }
            if (need == 0) break;
        }
    }

    uint32_t maxsublevel = 0;
    uint32_t at = 0;
    for (uint32_t i = 0; i < ret->size(); i++) {
        Lit l = (*ret)[i];
        if (varData[l.var()].sublevel >= maxsublevel) {
            maxsublevel = varData[l.var()].sublevel;
            at = i;
        }
    }
    std::swap((*ret)[0], (*ret)[at]);
}

void PropEngine::get_bnn_prop_reason(BNN *bnn, Lit lit, vector<Lit> *ret)
{
    assert(bnn->set || value(bnn->out) != l_Undef);
    assert(value(lit) == l_True); //it's being propagated

    if (lit.var() == bnn->out.var()) {
        // bnn->out got set

        //It's set to TRUE
        if (value(bnn->out) == l_True) {
            ret->clear();
            ret->push_back(lit); //this is what's propagated, must be 1st

            //Caused it to meet cutoff
            int32_t need = bnn->cutoff;
            for (const auto &l: *bnn) {
                if (varData[l.var()].sublevel <= varData[lit.var()].sublevel && value(l) == l_True) {
                    need--;
                    ret->push_back(~l);
                }
                if (need == 0) break;
            }
        }

        //it's set to FALSE
        if (value(bnn->out) == l_False) {
            ret->clear();
            ret->push_back(lit); //this is what's propagated, must be 1st

            //Caused it to meet cutoff
            int32_t need = bnn->size() - bnn->cutoff + 1;
            for (const auto &l: *bnn) {
                if (varData[l.var()].sublevel <= varData[lit.var()].sublevel && value(l) == l_False) {
                    need--;
                    ret->push_back(l);
                }
                if (need == 0) break;
            }
        }
        return;
    } else {
        // bnn->in got set

        ret->clear();
        ret->push_back(lit); //this is what's propagated, must be 1st
        if (!bnn->set) {
            ret->push_back(bnn->out ^ (value(bnn->out) == l_True));
        }
        for (const auto &l: *bnn) {
            if (varData[l.var()].sublevel < varData[lit.var()].sublevel) {
                if (bnn->set || (!bnn->set && value(bnn->out) == l_True)) {
                    if (value(l) == l_False) {
                        ret->push_back(l);
                    }
                }
                if (!bnn->set && value(bnn->out) == l_False) {
                    if (value(l) == l_True) {
                        ret->push_back(~l);
                    }
                }
            }
        }
        return;
    }
    assert(false);
}

/**
@brief Propagates a binary clause

Need to be somewhat tricky if the clause indicates that current assignment
is incorrect (i.e. both literals evaluate to FALSE). If conflict if found,
sets failBinLit
*/
template<bool inprocess>
inline bool PropEngine::prop_bin_cl(const Watched *i, const Lit p, PropBy &confl, uint32_t currLevel)
{
    const lbool val = value(i->lit2());
    if (val == l_Undef) {
        enqueue<inprocess>(i->lit2(), currLevel, PropBy(~p, i->red(), i->get_id()));
    } else if (val == l_False) {
        confl = PropBy(~p, i->red(), i->get_id());
        failBinLit = i->lit2();
        qhead = trail.size();
        return false;
    }

    return true;
}

template<bool inprocess, bool red_also, bool use_disable>
bool PropEngine::prop_long_cl_any_order(Watched *i, Watched *&j, const Lit p, PropBy &confl, uint32_t currLevel)
{
    //Blocked literal is satisfied, so clause is satisfied
    if (value(i->getBlockedLit()) == l_True) {
        *j++ = *i;
        return true;
    }
    if (inprocess) propStats.bogoProps += 4;
    const ClOffset offset = i->get_offset();
    Clause &c = *cl_alloc.ptr(offset);

#ifdef SLOW_DEBUG
    assert(!c.get_removed());
    assert(!c.freed());
    if (!use_disable) {
        assert(!c.disabled);
    }
#endif

    if (!red_also && c.red()) {
        *j++ = *i;
        return true;
    }

    if (use_disable && c.disabled) {
        *j++ = *i;
        return true;
    }

    if (prop_normal_helper<inprocess>(c, offset, j, p) == PROP_NOTHING) return true;

    // Did not find watch -- clause is unit under assignment:
    *j++ = *i;
    if (value(c[0]) == l_False) {
        handle_normal_prop_fail<inprocess>(c, offset, confl);
        return false;
    } else {
        if (!inprocess) {
#if defined(STATS_NEEDED) || defined(FINAL_PREDICTOR)
            c.stats.props_made++;
            c.stats.last_touched_any = sumConflicts;
#endif
        }

        if (currLevel == decisionLevel()) {
            enqueue<inprocess>(c[0], currLevel, PropBy(offset));
        } else {
            uint32_t nMaxLevel = currLevel;
            uint32_t nMaxInd = 1;
            // pass over all the literals in the clause and find the one with the biggest level
            for (uint32_t nInd = 2; nInd < c.size(); ++nInd) {
                uint32_t nLevel = varData[c[nInd].var()].level;
                if (nLevel > nMaxLevel) {
                    nMaxLevel = nLevel;
                    nMaxInd = nInd;
                }
            }

            if (nMaxInd != 1) {
                std::swap(c[1], c[nMaxInd]);
                j--; // undo last watch
                watches[c[1]].push(*i);
            }

            enqueue<inprocess>(c[0], nMaxLevel, PropBy(offset));
        }
    }

    return true;
}

void CMSat::PropEngine::reverse_one_bnn(uint32_t idx, BNNPropType t)
{
    BNN *const bnn = bnns[idx];
    SLOW_DEBUG_DO(assert(bnn != nullptr));
    switch (t) {
        case bnn_neg_t:
            bnn->ts--;
            bnn->undefs++;
            break;
        case bnn_pos_t:
            bnn->undefs++;
            break;
        case bnn_out_t:
            break;
    }
    VERBOSE_PRINT("reverse bnn idx: " << idx << " bnn->undefs: " << bnn->undefs << " bnn->ts: " << bnn->ts
                                      << " bnn->sz: " << bnn->size() << " BNN: " << *bnn);

    SLOW_DEBUG_DO(assert(bnn->ts >= 0));
    SLOW_DEBUG_DO(assert(bnn->undefs >= 0));
    SLOW_DEBUG_DO(assert(bnn->ts <= (int32_t)bnn->size()));
    SLOW_DEBUG_DO(assert(bnn->undefs <= (int32_t)bnn->size()));
}

void CMSat::PropEngine::reverse_prop(const CMSat::Lit l)
{
    if (!varData[l.var()].propagated) return;
    watch_subarray ws = watches[~l];
    for (const auto &i: ws) {
        if (i.isBNN()) {
            reverse_one_bnn(i.get_bnn(), i.get_bnn_prop_t());
        }
    }
    varData[l.var()].propagated = false;
}

template<bool inprocess, bool red_also, bool distill_use> PropBy PropEngine::propagate_any_order()
{
    PropBy confl;
    VERBOSE_PRINT("propagate_any_order started");

    while (qhead < trail.size() && confl.isnullptr()) {
        const Lit p = trail[qhead].lit; // 'p' is enqueued fact to propagate.
        varData[p.var()].propagated = true;
        watch_subarray ws = watches[~p];
        uint32_t currLevel = trail[qhead].lev;

        eq_elim(p);

        Watched *i = ws.begin();
        Watched *j = i;
        Watched *end = ws.end();
        if (inprocess) {
            propStats.bogoProps += ws.size() / 4 + 1;
        }
        propStats.propagations++;
        simpDB_props--;
        for (; i != end; i++) {
            // propagate binary clause
            if (likely(i->isBin())) {
                *j++ = *i;
                if (!red_also && i->red()) continue;
                if (distill_use && i->bin_cl_marked()) continue;
                prop_bin_cl<inprocess>(i, p, confl, currLevel);
                continue;
            }

            // propagate BNN constraint
            if (i->isBNN()) {
                *j++ = *i;
                const lbool val = bnn_prop(i->get_bnn(), currLevel, p, i->get_bnn_prop_t());
                if (val == l_False) confl = PropBy(i->get_bnn(), nullptr);
                continue;
            }

            //propagate normal clause
            assert(i->isClause());
            prop_long_cl_any_order<inprocess, red_also, distill_use>(i, j, p, confl, currLevel);
        }
        while (i != end) {
            *j++ = *i++;
        }
        ws.shrink_(end - j);
        VERBOSE_PRINT("prop went through watchlist of " << p);

        //distillation would need to generate TBDD proofs to simplify clauses with GJ
        if (!distill_use && confl.isnullptr()) confl = gauss_jordan_elim(p, currLevel);

        qhead++;
    }

#ifdef SLOW_DEBUG
    if (confl.isnullptr()) {
        for (size_t g = 0; g < gqueuedata.size(); g++) {
            if (gqueuedata[g].disabled) continue;
            gmatrices[g]->check_invariants();
        }
    }
#endif

    // For BNN debugging
    //     if (confl.isnullptr()) {
    //         for(uint32_t idx = 0; idx < bnns.size(); idx++) {
    //             auto& bnn = bnns[idx];
    //             if (!bnn) continue;
    //             int32_t undefs = 0;
    //             int32_t ts = 0;
    //             for(const auto& l: *bnn) {
    //                 if (value(l) == l_True) {
    //                     ts++;
    //                 }
    //                 if (value(l) == l_Undef) {
    //                     undefs++;
    //                 }
    //             }
    //             cout << "u: " << undefs << " my u: " << bnn->undefs << " -- ";
    //             cout << "t: " << ts << " my t: " << bnn->ts << " idx: " << idx
    //             << " sz :" << bnn->size() << endl;
    //             assert(undefs == bnn->undefs);
    //             assert(ts == bnn->ts);
    //         }
    //         cout << "ALL BNNS CHECKED========" << endl;
    //     }


    VERBOSE_PRINT("Propagation (propagate_any_order) ended.");

    return confl;
}
template PropBy PropEngine::propagate_any_order<false>();
template PropBy PropEngine::propagate_any_order<true>();
template PropBy PropEngine::propagate_any_order<true, false, true>();
template PropBy PropEngine::propagate_any_order<true, true, true>();


void PropEngine::printWatchList(const Lit lit) const
{
    watch_subarray_const ws = watches[lit];
    for (const Watched *it2 = ws.begin(), *end2 = ws.end(); it2 != end2; it2++) {
        if (it2->isBin()) {
            cout << "bin: " << lit << " , " << it2->lit2() << " red : " << (it2->red()) << endl;
        } else if (it2->isClause()) {
            cout << "cla:" << it2->get_offset() << endl;
        } else {
            assert(false);
        }
    }
}

void PropEngine::updateVars([[maybe_unused]] const vector<uint32_t> &outer_to_inter,
                            [[maybe_unused]] const vector<uint32_t> &inter_to_outer)
{
    //Trail is NOT correct, only its length is correct
    for (Trail &t: trail) t.lit = lit_Undef;
}

void PropEngine::print_trail()
{
    for (size_t i = trail_lim[0]; i < trail.size(); i++) {
        assert(varData[trail[i].lit.var()].level == trail[i].lev);
        cout << "trail " << i << ":" << trail[i].lit << " lev: " << trail[i].lev
             << " reason: " << varData[trail[i].lit.var()].reason << endl;
    }
}

template<bool inprocess> bool PropEngine::propagate_occur(int64_t *limit_to_decrease)
{
    assert(ok);
    bool ret = true;

    while (qhead < trail.size()) {
        const Lit p = trail[qhead].lit;
        qhead++;
        watch_subarray ws = watches[~p];

        //Go through each occur
        *limit_to_decrease -= 1;
        for (const auto &w: ws) {
            if (w.isClause()) {
                *limit_to_decrease -= 1;
                if (!prop_long_cl_occur<inprocess>(w.get_offset())) ret = false;
            }
            if (w.isBin())
                if (!prop_bin_cl_occur<inprocess>(w)) ret = false;
            assert(!w.isBNN());
        }
    }
    assert(gmatrices.empty());

    if (decisionLevel() == 0 && !ret) {
        *frat << add << ++clauseID << fin;
        set_unsat_cl_id(clauseID);
    }

    return ret;
}

template bool PropEngine::propagate_occur<true>(int64_t *);
template bool PropEngine::propagate_occur<false>(int64_t *);

template<bool inprocess> inline bool PropEngine::prop_bin_cl_occur(const Watched &ws)
{
    const lbool val = value(ws.lit2());
    if (val == l_False) return false;
    if (val == l_Undef) enqueue<inprocess>(ws.lit2());
    return true;
}

template<bool inprocess> inline bool PropEngine::prop_long_cl_occur(const ClOffset offset)
{
    const Clause &cl = *cl_alloc.ptr(offset);
    assert(!cl.freed() && "Cannot be already freed in occur");
    if (cl.get_removed()) return true;

    Lit lastUndef = lit_Undef;
    uint32_t numUndef = 0;
    bool satcl = false;
    for (const Lit lit: cl) {
        const lbool val = value(lit);
        if (val == l_True) {
            satcl = true;
            break;
        }
        if (val == l_Undef) {
            numUndef++;
            if (numUndef > 1) break;
            lastUndef = lit;
        }
    }
    if (satcl) return true;
    if (numUndef == 0) return false; //Problem is UNSAT
    if (numUndef > 1) return true;

    enqueue<inprocess>(lastUndef);
    return true;
}

#ifdef STATS_NEEDED_BRANCH
void PropEngine::sql_dump_vardata_picktime(uint32_t v, PropBy from)
{
    if (!solver->sqlStats) return;

    bool dump = false;
    double rnd_num = solver->mtrand.randDblExc();
    if (rnd_num <= conf.dump_individual_cldata_ratio * 0.1) {
        dump = true;
    }
    varData[v].dump = dump;
    if (!dump) return;

    solver->dump_restart_sql(rst_dat_type::var);

    uint64_t outer_var = map_inter_to_outer(v);

    varData[v].sumDecisions_at_picktime = sumDecisions;
    varData[v].sumConflicts_at_picktime = sumConflicts;
    varData[v].sumAntecedents_at_picktime = sumAntecedents;
    varData[v].sumAntecedentsLits_at_picktime = sumAntecedentsLits;
    varData[v].sumConflictClauseLits_at_picktime = sumConflictClauseLits;
    varData[v].sumPropagations_at_picktime = sumPropagations;
    varData[v].sumDecisionBasedCl_at_picktime = sumDecisionBasedCl;
    varData[v].sumClLBD_at_picktime = sumClLBD;
    varData[v].sumClSize_at_picktime = sumClSize;
    double rel_activity_at_picktime = std::log2(var_act_vsids[v] + 10e-300) / std::log2(max_vsids_act + 10e-300);

    varData[v].last_time_set_was_dec = (from == PropBy());

    //inside data
    varData[v].inside_conflict_clause_glue_at_picktime = varData[v].inside_conflict_clause_glue;
    varData[v].inside_conflict_clause_at_picktime = varData[v].inside_conflict_clause;
    varData[v].inside_conflict_clause_antecedents_at_picktime = varData[v].inside_conflict_clause_antecedents;

    solver->sqlStats->var_data_picktime(solver, outer_var, varData[v], rel_activity_at_picktime);
}
#endif

///// VMTF ////

void PropEngine::vmtf_check_unassigned()
{
    uint32_t at = vmtf_queue.unassigned;
    uint32_t unassigned = 0;
    while (at != numeric_limits<uint32_t>::max()) {
        at = vmtf_links[at].next;
        if (at != numeric_limits<uint32_t>::max()) {
            if (value(at) == l_Undef && varData[at].removed == Removed::none) {
                cout << "vmtf OOOPS, var " << at + 1 << " would have been unassigned. btab[var]: " << vmtf_btab[at]
                     << endl;
                unassigned++;
            }
        }
    }
    if (unassigned) {
        cout << "unassigned total: " << unassigned << endl;
        assert(unassigned == 0);
    }
}

uint32_t PropEngine::vmtf_pick_var()
{
    uint64_t searched = 0;
    uint32_t res = vmtf_queue.unassigned;
    VERBOSE_PRINT("vmtf start unassigned: " << res);

    SLOW_DEBUG_DO(vmtf_check_unassigned());
    while (res != numeric_limits<uint32_t>::max() && value(res) != l_Undef) {
        res = vmtf_links[res].prev;
        searched++;
    }

    if (res == numeric_limits<uint32_t>::max()) {
        vmtf_check_unassigned();
        return var_Undef;
    }
    if (searched) vmtf_update_queue_unassigned(res);
    VERBOSE_PRINT("vmtf next queue decision variable " << res << " btab value: " << vmtf_btab[res]);
    return res;
}

// Update queue to point to last potentially still unassigned variable.
// All variables after 'queue.unassigned' in bump order are assumed to be
// assigned.  Then update the 'queue.vmtf_bumped' field and log it.
void PropEngine::vmtf_update_queue_unassigned(const uint32_t var)
{
    assert(var != numeric_limits<uint32_t>::max());
    assert(var < nVars());
    VERBOSE_PRINT("vmtf_queue.unassigned set to: " << var + 1 << " vmtf_queue.vmtf_bumped set to: " << vmtf_btab[var]);
    vmtf_queue.unassigned = var;
    vmtf_queue.vmtf_bumped = vmtf_btab[var];
}

void PropEngine::vmtf_init_enqueue(const uint32_t var)
{
    assert(var < nVars());
    assert(var < vmtf_links.size());
    Link &l = vmtf_links[var];

    //Put at the end of the queue
    l.next = numeric_limits<uint32_t>::max();
    if (vmtf_queue.last != numeric_limits<uint32_t>::max()) {
        // Not empty queue
        assert(vmtf_links[vmtf_queue.last].next == numeric_limits<uint32_t>::max());
        vmtf_links[vmtf_queue.last].next = var;
    } else {
        // Empty queue
        assert(vmtf_queue.first == numeric_limits<uint32_t>::max());
        vmtf_queue.first = var;
    }
    l.prev = vmtf_queue.last;
    vmtf_queue.last = var;

    vmtf_btab[var] = ++stats_bumped; // set timestamp of enqueue
    vmtf_update_queue_unassigned(vmtf_queue.last);
}

void PropEngine::vmtf_dequeue(const uint32_t var)
{
    Link &l = vmtf_links[var];
    if (vmtf_queue.unassigned == var) {
        vmtf_queue.unassigned = l.prev;
        if (vmtf_queue.unassigned != numeric_limits<uint32_t>::max()) {
            vmtf_update_queue_unassigned(vmtf_queue.unassigned);
        }
    }
    //vmtf_queue.dequeue (vmtf_links, var);
}

// Move vmtf_bumped variables to the front of the (VMTF) decision queue.  The
// 'vmtf_bumped' time stamp is updated accordingly.  It is used to determine
// whether the 'queue.assigned' pointer has to be moved in 'unassign'.

void PropEngine::vmtf_bump_queue(const uint32_t var)
{
    if (vmtf_links[var].next == numeric_limits<uint32_t>::max()) {
        return;
    }
    //Remove from wherever it is, put to the end
    vmtf_queue.dequeue(vmtf_links, var);
    vmtf_queue.enqueue(vmtf_links, var);

    assert(stats_bumped != numeric_limits<uint64_t>::max());
    vmtf_btab[var] = ++stats_bumped;
    VERBOSE_PRINT("vmtf moved to last element in queue the variable " << var + 1 << " and vmtf_bumped to "
                                                                      << vmtf_btab[var]);
    if (value(var) == l_Undef) vmtf_update_queue_unassigned(var);
}


// Helper function: Create a literal for reason clause that is False under current assignment
// Rule: if value(v)==True, return ¬v; if value(v)==False, return v
static inline Lit make_reason_lit(uint32_t var, const PropEngine *engine)
{
    lbool var_val = engine->value(var);
    if (var_val == l_True) {
        return Lit(var, true);  // ¬v, which is False when v=True
    } else {
        return Lit(var, false); // v, which is False when v=False
    }
}

// Unified canonicalization: Resolve alias and create literal that is False under current assignment
// This ensures all literals in reason clause use canonical representatives and are False
static inline Lit make_canonical_reason_lit(const Lit orig, PropEngine *engine)
{
    // Step 1: Resolve alias to get canonical representative (with sign preserved)
    Lit resolved = engine->resolve_alias(orig);
    
    // Step 2: Create literal that is False under current assignment
    // If resolved.var() is True -> need literal ¬var (sign = true)
    // If resolved.var() is False -> need literal var (sign = false)
    bool assign_true = (engine->value(resolved.var()) == l_True);
    Lit lit_false = Lit(resolved.var(), assign_true);
    
    // Verify the result is indeed False
    assert(engine->value(lit_false) == l_False && "make_canonical_reason_lit must return False literal");
    
    return lit_false;
}

vector<Lit> *PropEngine::get_xor_reason(const PropBy &reason, int32_t &ID, Lit target_lit)
{
    frat_func_start();

    if (reason.get_matrix_num() != 1000) {
        auto *ret = gmatrices[reason.get_matrix_num()]->get_reason(reason.get_row_num(), ID);
        frat_func_end();
        return ret;
    }

    auto &x = xorclauses[reason.get_row_num()];

    if (frat->enabled()) {
        if (x.reason_cl_ID != 0) *frat << del << x.reason_cl_ID << x.reason_cl << fin;
        x.reason_cl_ID = 0;
    }

    // Keep active set in sync with the latest alias structure
    update_xor_active_vars(reason.get_row_num());

    const bool is_propagation = (target_lit != lit_Undef);
    x.reason_cl.clear();

    auto assigned_at_event = [&](uint32_t var) {
        const auto &vd = varData[var];
        if (vd.level < x.prop_level) return true;
        if (vd.level > x.prop_level) return false;
        return vd.sublevel <= x.prop_sublevel;
    };

    auto lit_with_value = [&](uint32_t var, bool want_true, lbool hint = l_Undef) {
        lbool v = value(var);
        if (v == l_Undef) v = hint;
        bool sign = want_true ? (v == l_False) : (v == l_True);
        return Lit(var, sign);
    };

    uint32_t target_var = var_Undef;
    lbool target_val = l_Undef;
    if (is_propagation) {
        Lit resolved = resolve_alias(target_lit);
        target_var = resolved.var();
        target_val = value(target_var);
    }

    vector<Lit> aux_lits;
    bool parity = false;
    for (uint32_t rvar : x.active_resolved_vars) {
        if (is_propagation && rvar == target_var) continue;
        lbool v = value(rvar);
        if (v == l_Undef) continue;
        if (!assigned_at_event(rvar)) continue;
        parity ^= (v == l_True);
        aux_lits.push_back(lit_with_value(rvar, false, v));
    }

    for (const Lit &factor : x.last_used_factors) {
        Lit f = resolve_alias(factor);
        uint32_t v = f.var();
        if (!assigned_at_event(v)) continue;
        if (value(v) != l_True) continue;
        aux_lits.push_back(lit_with_value(v, false, l_True));
    }

    std::sort(aux_lits.begin(), aux_lits.end());
    aux_lits.erase(std::unique(aux_lits.begin(), aux_lits.end()), aux_lits.end());

    if (is_propagation) {
        lbool expected = l_Undef;
        if (target_val == l_Undef) {
            expected = (parity != x.rhs) ? l_True : l_False;
        }

        Lit first = lit_with_value(target_var, true, target_val == l_Undef ? expected : target_val);
        x.reason_cl.push_back(first);

        aux_lits.erase(std::remove(aux_lits.begin(), aux_lits.end(), first), aux_lits.end());
        x.reason_cl.insert(x.reason_cl.end(), aux_lits.begin(), aux_lits.end());
    } else {
        x.reason_cl.swap(aux_lits);
        if (!x.reason_cl.empty()) {
            size_t best = 0;
            uint32_t best_level = 0;
            uint32_t best_sub = 0;
            for (size_t i = 0; i < x.reason_cl.size(); i++) {
                uint32_t lvl = varData[x.reason_cl[i].var()].level;
                uint32_t sub = varData[x.reason_cl[i].var()].sublevel;
                if (lvl > best_level || (lvl == best_level && sub >= best_sub)) {
                    best_level = lvl;
                    best_sub = sub;
                    best = i;
                }
            }
            std::swap(x.reason_cl[0], x.reason_cl[best]);
        }
    }

    if (x.reason_cl.empty() && !x.active_resolved_vars.empty()) {
        uint32_t v = x.active_resolved_vars.front();
        x.reason_cl.push_back(lit_with_value(v, false));
    }

    if (frat->enabled()) {
        x.reason_cl_ID = ++clauseID;
        *frat << implyclfromx << x.reason_cl_ID << x.reason_cl << FratFlag::fratchain << x.xid << fin;
        ID = x.reason_cl_ID;
    }

    frat_func_end();
    return &x.reason_cl;
}
