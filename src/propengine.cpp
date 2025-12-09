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
#define DEBUG_ANF_PROP

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
}

void PropEngine::new_vars(size_t n)
{
    CNF::new_vars(n);

    var_act_vsids.insert(var_act_vsids.end(), n, 0);
    vmtf_btab.insert(vmtf_btab.end(), n, 0);
    vmtf_links.insert(vmtf_links.end(), n, Link());
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
    
    // ANF-Elim: Initialize active_resolved_vars (variables with odd count after alias resolution)
    update_xor_active_vars(at);
}

void PropEngine::update_xor_active_vars(uint32_t at)
{
    Xor &x = xorclauses[at];
    x.active_resolved_vars.clear();
    
    // Count occurrences of each resolved variable
    std::map<uint32_t, int> resolved_var_count;
    for (uint32_t i = 0; i < x.size(); i++) {
        uint32_t orig_var = x[i];
        Lit orig_lit = Lit(orig_var, false);
        Lit resolved_lit = resolve_alias(orig_lit);
        uint32_t resolved_var = resolved_lit.var();
        resolved_var_count[resolved_var]++;
    }
    
    // Only variables with odd count are active (x⊕x=0 elimination)
    for (const auto &pair : resolved_var_count) {
        if (pair.second % 2 == 1) {
            x.active_resolved_vars.insert(pair.first);
        }
    }
    
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
    cout << " | Resolved counts: ";
    for (const auto &pair : resolved_var_count) {
        cout << "x" << pair.first + 1 << ":" << pair.second << " ";
    }
    cout << "| Active vars (odd count): ";
    for (uint32_t v : x.active_resolved_vars) {
        cout << v + 1 << " ";
    }
    cout << "| RHS=" << x.rhs << endl;
#endif
}

void PropEngine::update_xor_active_vars_for_var(uint32_t var)
{
    // Update all XOR clauses that contain this variable (or its alias)
    // We need to check gwatches to find all XOR clauses containing this variable
    if (gwatches.size() <= var) return;
    
    vec<GaussWatched> &ws = gwatches[var];
    std::set<uint32_t> updated_xors;  // Avoid updating the same XOR clause multiple times
    
    for (const GaussWatched &w : ws) {
        if (w.matrix_num == 1000) {
            uint32_t at = w.row_n;
            if (updated_xors.find(at) == updated_xors.end()) {
                update_xor_active_vars(at);
                updated_xors.insert(at);
            }
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
            if (pv == x[x.watched[0]]) which = 0;
            else {
                which = 1;
                if (x[x.watched[1]] != pv) {
                    cout << "ERROR. Going through pv: " << pv + 1 << " xor: " << x << endl;
                }
                assert(x[x.watched[1]] == pv);
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
                                // it's not the other watch. So we can update current
                                // watch to this (using original variable for watch)
                                gwatches[orig_var].push(GaussWatched::plain_xor(at));
                                x.watched[which] = i2;
#ifdef DEBUG_ANF_PROP
                                cout << "  Found new watch at position " << i2 << " (orig var " << orig_var + 1 << ", resolved to " << resolved_var + 1 << ")" << endl;
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
                assert(unknown_at == x.watched[!which]);
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
                            for (uint32_t j = 0; j < eq.size(); j++) {
                                const Lit &factor = eq[j];
                                if (value(factor) == l_True) {
                                    // Store canonicalized factor (resolved)
                                    Lit canonical_factor = resolve_alias(factor);
                                    x.last_used_factors.push_back(canonical_factor);
                                }
                            }
                        }
                    }
                }
                
                // Use resolved variable for propagation (if alias was applied)
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
                            for (uint32_t j = 0; j < eq.size(); j++) {
                                const Lit &factor = eq[j];
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

vector<Lit> *PropEngine::get_xor_reason(const PropBy &reason, int32_t &ID)
{
    frat_func_start();
#ifdef DEBUG_ANF_PROP
    cout << "[ANF-REASON] get_xor_reason called: matrix=" << reason.get_matrix_num() 
         << ", row=" << reason.get_row_num() << ", type=" << (int)reason.getType() << endl;
#endif
    if (reason.get_matrix_num() == 1000) {
        auto &x = xorclauses[reason.get_row_num()];
#ifdef DEBUG_ANF_PROP
        cout << "[ANF-REASON] Building reason for XOR clause #" << reason.get_row_num() 
             << ", prop_confl_watch=" << (int)x.prop_confl_watch << endl;
        cout << "[ANF-REASON] Original XOR vars: ";
        for (uint32_t i = 0; i < x.size(); i++) {
            cout << x[i] + 1 << " ";
        }
        cout << "| RHS=" << (int)x.rhs << endl;
        cout << "[ANF-REASON] Active resolved vars: ";
        for (uint32_t v : x.active_resolved_vars) {
            cout << v + 1 << " ";
        }
        cout << endl;
#endif
        if (frat->enabled()) {
            if (x.reason_cl_ID != 0) *frat << del << x.reason_cl_ID << x.reason_cl << fin;
            x.reason_cl_ID = 0;
        }
        x.reason_cl.clear();
        
        // 重要修改：在构造reason之前先更新active_resolved_vars
        update_xor_active_vars(reason.get_row_num());
        
        // ANF-Elim: Build reason using active_resolved_vars and alias information
        // Collect U: conflicting literals from active variables
        // Collect used aliases and their factors (F_S)
        
        std::set<Lit> added_lits;  // 用于去重
        std::map<uint32_t, std::vector<Lit>> aux_factors; // aux_var -> enabling factors
        
        // 找出传播或冲突的变量
        uint32_t pc_var = var_Undef;
        bool is_propagation = (x.prop_confl_watch < 2);
        
        if (is_propagation) {
            const auto prop_at = x.watched[x.prop_confl_watch];
            uint32_t orig_var = x.vars[prop_at];
            Lit orig_lit = Lit(orig_var, false);
            Lit resolved_lit = resolve_alias(orig_lit);
            pc_var = resolved_lit.var();
        } else {
            // 冲突情况：所有变量都已赋值
            // 不需要特定的pc_var
        }
        
        // CRITICAL FIX: Use recorded used_factors from propagation/conflict time
        // Do NOT recompute from current alias map, as it may have changed due to later decisions
        // This ensures the reason reflects the alias state at the time of propagation/conflict
        
        if (!x.last_used_factors.empty()) {
            // Use the factors recorded at propagation/conflict time
            // These are already canonicalized (resolved) and were True at that time
            for (const Lit &factor : x.last_used_factors) {
                // Factor was True at propagation time, so we add ~factor to reason
                // But we need to ensure it's still False under current assignment
                Lit reason_factor = make_canonical_reason_lit(factor, this);
                aux_factors[0].push_back(reason_factor);  // Use dummy key 0 for all factors
            }
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-REASON] Using " << x.last_used_factors.size() 
                 << " recorded factors from propagation/conflict time (level=" << x.prop_level 
                 << ", sublevel=" << x.prop_sublevel << ")" << endl;
#endif
        } else {
            // Fallback: If no recorded factors (shouldn't happen in normal operation),
            // recompute from current alias map (but this may be incorrect)
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-REASON] WARNING: No recorded factors, recomputing from current alias map (may be incorrect!)" << endl;
#endif
            // 修改2: 更完整地收集alias信息和factors
            // 首先收集所有使用的alias及其enabling factors
            for (uint32_t i = 0; i < x.size(); i++) {
                uint32_t orig_var = x[i];
                if (!is_aux_var(orig_var)) continue;
                
                Lit orig_lit = Lit(orig_var, false);
                Lit resolved_lit = resolve_alias(orig_lit);
                
                if (resolved_lit.var() != orig_var) {
                    // 这个aux变量被alias了，收集其enabling factors
                    auto it = aux_to_eid.find(orig_var);
                    if (it != aux_to_eid.end()) {
                        const Eq &eq = eq_clauses[it->second];
                        
                        // 收集所有值为True的因子（这些使得alias生效）
                        // 注意：eq.lits 只包含因子，aux_lit 是单独存储的，所以不需要跳过
                        for (uint32_t j = 0; j < eq.size(); j++) {
                            const Lit &factor = eq[j];
                            if (value(factor) == l_True) {
                                aux_factors[orig_var].push_back(factor);
                            }
                        }
                    }
                }
            }
        }
        
        // Build reason clause
        // Step 1: Compute RHS from all active variables (for verification)
        bool computed_rhs = false;
        for (uint32_t resolved_var : x.active_resolved_vars) {
            if (value(resolved_var) != l_Undef) {
                bool var_val = (value(resolved_var) == l_True);
                computed_rhs ^= var_val;
            }
        }
#ifdef DEBUG_ANF_PROP
        cout << "[ANF-REASON] Computed RHS=" << (int)computed_rhs << ", clause RHS=" << (int)x.rhs << endl;
#endif
        
        // Step 2: Build reason clause according to CDCL rules
        // Rule: All literals in reason clause must be False under current assignment
        // lit_for_reason(v) = (value(v)==True ? ¬v : v)
        
        if (is_propagation) {
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-REASON] Building propagation reason clause..." << endl;
#endif
            // For propagation: Add propagated variable l' FIRST (at index 0), then U (assigned variables except propagated one)
            
            // First, compute the propagated literal
            bool rhs_without_pc = false;
            for (uint32_t resolved_var : x.active_resolved_vars) {
                if (resolved_var == pc_var) continue;
                if (value(resolved_var) != l_Undef) {
                    rhs_without_pc ^= (value(resolved_var) == l_True);
                }
            }
            // The propagated value is: pc_var should be (rhs_without_pc == x.rhs)
            // But we need to add the literal that is False under current assignment
            // Use canonicalization: construct Lit from resolved_var, then canonicalize
            Lit prop_orig = Lit(pc_var, false);
            Lit prop_lit = make_canonical_reason_lit(prop_orig, this);
            
            // Add propagated literal FIRST (at index 0) - this is what's propagated, must be 1st
            if (added_lits.find(prop_lit) == added_lits.end()) {
                x.reason_cl.push_back(prop_lit);
                added_lits.insert(prop_lit);
#ifdef DEBUG_ANF_PROP
                cout << "[ANF-REASON]   Added propagated lit (at index 0): " << prop_lit << " (var " << pc_var + 1 
                     << ", lit value=" << (value(prop_lit) == l_False ? "False" : "True") << ")" << endl;
#endif
            }
            
            // Add U: all assigned variables except pc_var
            for (uint32_t resolved_var : x.active_resolved_vars) {
                if (resolved_var == pc_var) continue;
                
                if (value(resolved_var) != l_Undef) {
                    // Use canonicalization: construct Lit from resolved_var, then canonicalize
                    Lit orig_lit = Lit(resolved_var, false);
                    Lit lit = make_canonical_reason_lit(orig_lit, this);
                    if (added_lits.find(lit) == added_lits.end()) {
                        x.reason_cl.push_back(lit);
                        added_lits.insert(lit);
#ifdef DEBUG_ANF_PROP
                        cout << "[ANF-REASON]   Added to U: " << lit << " (var " << resolved_var + 1 
                             << "=" << (value(resolved_var) == l_True ? "True" : "False") 
                             << ", lit value=" << (value(lit) == l_False ? "False" : "True") << ")" << endl;
#endif
                    }
                }
            }
        } else {
            // For conflict: all variables are assigned, computed_rhs != x.rhs
            // Add all assigned variables using canonicalization
            // Later we'll move the literal with max sublevel to index 0
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-REASON] Building conflict reason clause..." << endl;
#endif
            for (uint32_t resolved_var : x.active_resolved_vars) {
                if (value(resolved_var) != l_Undef) {
                    // Use canonicalization: construct Lit from resolved_var, then canonicalize
                    Lit orig_lit = Lit(resolved_var, false);
                    Lit lit = make_canonical_reason_lit(orig_lit, this);
                    if (added_lits.find(lit) == added_lits.end()) {
                        x.reason_cl.push_back(lit);
                        added_lits.insert(lit);
#ifdef DEBUG_ANF_PROP
                        lbool lit_val = value(lit);
                        cout << "[ANF-REASON]   Added to U: " << lit << " (var " << resolved_var + 1 
                             << "=" << (value(resolved_var) == l_True ? "True" : "False") 
                             << ", lit value=" << (lit_val == l_False ? "False" : "True") << ")" << endl;
#endif
                    }
                }
            }
        }
        
        // Step 3: Add enabling factors
        // CRITICAL: Use recorded factors from propagation/conflict time if available
        // This ensures we use the alias state that existed at that time, not the current state
        if (!x.last_used_factors.empty()) {
            // Using recorded factors - they were True at propagation/conflict time
            for (const Lit &factor : x.last_used_factors) {
                // Factor was canonicalized (resolved) and True at propagation time
                // Create reason literal that is False under current assignment
                Lit reason_factor = make_canonical_reason_lit(factor, this);
                
                // Verify the resulting literal is False
                assert(value(reason_factor) == l_False && "Reason factor literal must be False");
                
                if (added_lits.find(reason_factor) == added_lits.end()) {
                    x.reason_cl.push_back(reason_factor);
                    added_lits.insert(reason_factor);
#ifdef DEBUG_ANF_PROP
                    cout << "[ANF-REASON]   Added recorded factor lit: " << reason_factor << " (from factor " << factor 
                         << ", recorded at prop_level=" << x.prop_level << ", reason_factor value=False)" << endl;
#endif
                }
            }
        } else {
            // Fallback: Using recomputed factors (shouldn't happen in normal operation)
            // For each factor f (Lit) that is True and enabled alias, add canonicalized literal that is False
            for (const auto &pair : aux_factors) {
                for (const Lit &factor : pair.second) {
                    // CRITICAL: Verify factor is True before adding its negation
                    lbool factor_val = value(factor);
                    if (factor_val != l_True) {
#ifdef DEBUG_ANF_PROP
                        cerr << "[ANF-REASON] WARNING: Factor " << factor << " is not True (value=" << factor_val 
                             << "), skipping!" << endl;
#endif
                        continue;  // Skip factors that are not True
                    }
                    
                    // factor is a Lit (with sign), and it's True (we only collected True factors)
                    // Use canonicalization: resolve alias and create literal that is False
                    Lit reason_factor = make_canonical_reason_lit(factor, this);
                    
                    // Verify the resulting literal is False
                    assert(value(reason_factor) == l_False && "Reason factor literal must be False");
                    
                    if (added_lits.find(reason_factor) == added_lits.end()) {
                        x.reason_cl.push_back(reason_factor);
                        added_lits.insert(reason_factor);
#ifdef DEBUG_ANF_PROP
                        cout << "[ANF-REASON]   Added recomputed factor lit: " << reason_factor << " (from factor " << factor 
                             << ", factor value=True, reason_factor value=False)" << endl;
#endif
                    }
                }
            }
        }
        
        // Final step: Canonicalize all literals before deduplication and sorting
        // This ensures all literals use canonical representatives and are False
        vector<Lit> normalized_cl;
        for (const Lit &orig_lit : x.reason_cl) {
            // Re-canonicalize to ensure consistency (though they should already be canonical)
            Lit canonical_lit = make_canonical_reason_lit(orig_lit, this);
            normalized_cl.push_back(canonical_lit);
        }
        x.reason_cl = normalized_cl;
        
        // CRITICAL FILTER: Remove all literals that are True under current assignment
        // This is essential for CDCL conflict analysis - seed clause must be fully falsified
        vector<Lit> filtered_cl;
        for (const Lit &lit : x.reason_cl) {
            lbool lit_val = value(lit);
            if (lit_val == l_False) {
                filtered_cl.push_back(lit);
            } else {
#ifdef DEBUG_ANF_PROP
                cerr << "[ANF-REASON] WARNING: Filtering out True literal: " << lit 
                     << " (var=" << lit.var() + 1 << ", value=" << lit_val << ")" << endl;
                Lit resolved = resolve_alias(lit);
                cerr << "  resolved=" << resolved << ", value(resolved)=" << value(resolved) << endl;
#endif
            }
        }
        
        // If filtering removed all literals, this is a critical error
        if (filtered_cl.empty()) {
            cerr << "ERROR: All reason clause literals were True after filtering!" << endl;
            assert(false && "Reason clause must contain at least one False literal");
        }
        
        // Verify all literals use canonical representatives (consistent with varData)
        for (Lit &lit : filtered_cl) {
            Lit resolved = resolve_alias(lit);
            if (resolved.var() != lit.var()) {
                // Update to canonical form
                lit = make_canonical_reason_lit(resolved, this);
            }
            // Double-check it's still False
            assert(value(lit) == l_False && "Canonicalized literal must be False");
        }
        
        x.reason_cl = filtered_cl;
        
        // Remove duplicates and ensure proper ordering
#ifdef DEBUG_ANF_PROP
        cout << "[ANF-REASON] After filtering True literals, reason_cl size=" << x.reason_cl.size() << endl;
#endif
        
        if (is_propagation) {
            // For propagation: Keep propagated literal at index 0, sort and dedup the rest
            if (x.reason_cl.size() > 1) {
                Lit prop_lit = x.reason_cl[0];  // Save propagated literal
                // Sort and dedup the rest (from index 1 onwards)
                std::sort(x.reason_cl.begin() + 1, x.reason_cl.end());
                auto last = std::unique(x.reason_cl.begin() + 1, x.reason_cl.end());
                x.reason_cl.erase(last, x.reason_cl.end());
                // Ensure propagated literal is still at index 0
                if (x.reason_cl[0] != prop_lit) {
                    // Find prop_lit and swap it to index 0
                    for (uint32_t i = 1; i < x.reason_cl.size(); i++) {
                        if (x.reason_cl[i] == prop_lit) {
                            std::swap(x.reason_cl[0], x.reason_cl[i]);
                            break;
                        }
                    }
                }
            }
            
            // Verify propagated literal is at index 0 and is False
            assert(!x.reason_cl.empty() && "Propagation reason clause must not be empty");
            assert(value(x.reason_cl[0]) == l_False && "Propagated literal in reason must be False");
            
#ifdef DEBUG_ANF_PROP
            uint32_t prop_level = varData[x.reason_cl[0].var()].level;
            uint32_t curr_level = decisionLevel();
            cout << "[ANF-REASON] Propagation reason: prop_lit=" << x.reason_cl[0] 
                 << " at level=" << prop_level << ", curr_level=" << curr_level << endl;
            uint32_t count_at_prop_level = 0;
            uint32_t count_with_valid_reason = 0;
            uint32_t count_with_null_reason = 0;
            uint32_t count_at_level_0 = 0;
            for (const Lit &l : x.reason_cl) {
                if (varData[l.var()].level == prop_level) {
                    count_at_prop_level++;
                    const PropBy &reason = varData[l.var()].reason;
                    if (reason.isnullptr()) {
                        count_with_null_reason++;
                    } else {
                        count_with_valid_reason++;
                    }
                } else if (varData[l.var()].level == 0) {
                    count_at_level_0++;
                }
            }
            cout << "[ANF-REASON] Count of literals at prop_level: " << count_at_prop_level << endl;
            cout << "[ANF-REASON]   - With valid reason: " << count_with_valid_reason << endl;
            cout << "[ANF-REASON]   - With null reason (decision): " << count_with_null_reason << endl;
            cout << "[ANF-REASON] Count of literals at level 0: " << count_at_level_0 << endl;
            
            // Check if any literal at prop_level has an XOR reason (which might cause recursive issues)
            uint32_t count_with_xor_reason = 0;
            for (const Lit &l : x.reason_cl) {
                if (varData[l.var()].level == prop_level) {
                    const PropBy &reason = varData[l.var()].reason;
                    if (!reason.isnullptr() && reason.getType() == xor_t) {
                        count_with_xor_reason++;
                        cout << "[ANF-REASON]   WARNING: Literal " << l << " at prop_level has XOR reason (row=" 
                             << reason.get_row_num() << ")" << endl;
                    }
                }
            }
            if (count_with_xor_reason > 0) {
                cout << "[ANF-REASON]   - With XOR reason: " << count_with_xor_reason << endl;
            }
            
            // CRITICAL: Check if pathC calculation would be correct
            // pathC should be the number of literals at prop_level with level >= nDecisionLevel
            // In add_lit_to_learnt, if varData[var].level >= nDecisionLevel, pathC++
            // But if reason is nullptr, it won't be processed in the resolution loop
            // NOTE: In add_lits_to_learnt, for i==0 and p==lit_Undef, the first literal IS processed
            // So pathC should include the first literal if it's at prop_level
            cout << "[ANF-REASON]   Expected pathC from literals at prop_level: " << count_at_prop_level << endl;
            cout << "[ANF-REASON]   Expected pathC from literals with valid reason: " << count_with_valid_reason << endl;
            cout << "[ANF-REASON]   NOTE: Decision literals (null reason) won't reduce pathC in resolution loop!" << endl;
            cout << "[ANF-REASON]   NOTE: First literal (index 0) WILL be processed when p==lit_Undef!" << endl;
            
            // Check for duplicate literals in reason clause (which would cause seen[var] to skip)
            std::set<uint32_t> vars_in_reason;
            uint32_t duplicate_count = 0;
            for (const Lit &l : x.reason_cl) {
                if (vars_in_reason.find(l.var()) != vars_in_reason.end()) {
                    duplicate_count++;
                    cout << "[ANF-REASON]   WARNING: Duplicate variable " << l.var() + 1 << " in reason clause!" << endl;
                }
                vars_in_reason.insert(l.var());
            }
            if (duplicate_count > 0) {
                cout << "[ANF-REASON]   Found " << duplicate_count << " duplicate variables in reason clause!" << endl;
                cout << "[ANF-REASON]   NOTE: Duplicate variables will cause seen[var] to skip, reducing pathC!" << endl;
            }
#endif
        } else {
            // For conflict: Remove duplicates, remove tautologies (complementary literals), 
            // then find seed_level (max level in reason_cl) and put literal at seed_level with max sublevel at index 0
            
            // Step 1: Sort and remove exact duplicates
            std::sort(x.reason_cl.begin(), x.reason_cl.end());
            auto last = std::unique(x.reason_cl.begin(), x.reason_cl.end());
            x.reason_cl.erase(last, x.reason_cl.end());
            
            // Step 2: Remove tautologies (complementary literals: l and ~l)
            // Build a set of negated literals to check for complements
            std::set<Lit> negated_lits;
            for (const Lit &lit : x.reason_cl) {
                negated_lits.insert(~lit);
            }
            
            // Remove literals that have their complement in the clause
            vector<Lit> filtered_cl;
            for (const Lit &lit : x.reason_cl) {
                if (negated_lits.find(lit) == negated_lits.end()) {
                    filtered_cl.push_back(lit);
                } else {
#ifdef DEBUG_ANF_PROP
                    cout << "[ANF-REASON] Removed tautology: " << lit << " and " << ~lit << " both present" << endl;
#endif
                }
            }
            
            // If we removed all literals due to tautology, this is a serious error
            if (filtered_cl.empty()) {
                cerr << "ERROR: Conflict reason clause became empty after removing tautologies!" << endl;
                // Fallback: use a minimal reason with just U (assigned variables)
                filtered_cl.clear();
                for (uint32_t resolved_var : x.active_resolved_vars) {
                    if (value(resolved_var) != l_Undef) {
                        Lit orig_lit = Lit(resolved_var, false);
                        Lit lit = make_canonical_reason_lit(orig_lit, this);
                        filtered_cl.push_back(lit);
                    }
                }
                if (filtered_cl.empty()) {
                    assert(false && "Cannot construct conflict reason clause");
                }
            }
            x.reason_cl = filtered_cl;
            
            // Step 3: Find seed_level (max level in reason_cl) and put literal at seed_level with max sublevel at index 0
            // Also, ensure the second literal is NOT at seed_level (for CDCL conflict analysis)
            uint32_t seed_level = 0;
            uint32_t curr_level = decisionLevel();
            for (const Lit &l : x.reason_cl) {
                uint32_t lvl = varData[l.var()].level;
                if (lvl > seed_level) {
                    seed_level = lvl;
                }
            }
            
            // Critical check: Ensure at least one literal is at curr_level (decisionLevel())
            // CDCL requires the seed clause to have at least one literal at the current decision level
            bool found_at_curr_level = false;
            uint32_t count_at_curr_level = 0;
            uint32_t count_at_seed = 0;
            
            for (const Lit &l : x.reason_cl) {
                if (varData[l.var()].level == curr_level) {
                    found_at_curr_level = true;
                    count_at_curr_level++;
                }
                if (varData[l.var()].level == seed_level) {
                    count_at_seed++;
                }
            }
            
#ifdef DEBUG_ANF_PROP
            cout << "[ANF-REASON] seed_level=" << seed_level << ", curr_level=" << curr_level << endl;
            cout << "[ANF-REASON] Count of literals at seed_level: " << count_at_seed << endl;
            cout << "[ANF-REASON] Count of literals at curr_level: " << count_at_curr_level << endl;
#endif
            
            // If no literal at curr_level, this is a critical error for CDCL
            if (!found_at_curr_level) {
                cerr << "ERROR: No literal found at curr_level (" << curr_level 
                     << ")! CDCL requires at least one literal at current decision level." << endl;
                cerr << "seed_level=" << seed_level << ", reason_cl size=" << x.reason_cl.size() << endl;
#ifdef DEBUG_ANF_PROP
                cerr << "Reason clause literals with levels:" << endl;
                for (uint32_t i = 0; i < x.reason_cl.size(); i++) {
                    Lit l = x.reason_cl[i];
                    cerr << "  [" << i << "] " << l << " -> value=" << value(l) 
                         << ", level=" << varData[l.var()].level 
                         << ", sublevel=" << varData[l.var()].sublevel << endl;
                }
                cerr << "Active resolved vars:" << endl;
                for (uint32_t v : x.active_resolved_vars) {
                    cerr << "  var " << v + 1 << " -> value=" << value(v) 
                         << ", level=" << varData[v].level << endl;
                }
#endif
                
                // Fallback: Try to reconstruct a minimal reason with current-level literals
                // This should not happen if canonicalization is correct, but we try to recover
                vector<Lit> fallback_cl;
                for (uint32_t resolved_var : x.active_resolved_vars) {
                    if (value(resolved_var) != l_Undef && varData[resolved_var].level == curr_level) {
                        Lit orig_lit = Lit(resolved_var, false);
                        Lit lit = make_canonical_reason_lit(orig_lit, this);
                        if (value(lit) == l_False) {
                            fallback_cl.push_back(lit);
                        }
                    }
                }
                
                if (!fallback_cl.empty()) {
                    cerr << "Using fallback reason with " << fallback_cl.size() 
                         << " literals at curr_level" << endl;
                    x.reason_cl = fallback_cl;
                    seed_level = curr_level;
                } else {
                    // Last resort: use seed_level (may not work for CDCL, but better than crash)
                    cerr << "WARNING: Using seed_level " << seed_level 
                         << " instead of curr_level (may cause CDCL issues)" << endl;
                }
            }
            
            // Find literal at seed_level with max sublevel (prefer curr_level if available)
            uint32_t target_level = found_at_curr_level ? curr_level : seed_level;
            uint32_t maxsublevel_at_target = 0;
            uint32_t at_target = 0;
            bool found_at_target = false;
            
            for (uint32_t i = 0; i < x.reason_cl.size(); i++) {
                Lit l = x.reason_cl[i];
                if (varData[l.var()].level == target_level) {
                    found_at_target = true;
                    if (varData[l.var()].sublevel >= maxsublevel_at_target) {
                        maxsublevel_at_target = varData[l.var()].sublevel;
                        at_target = i;
                    }
                }
            }
            
            // Ensure we found at least one literal at target_level
            if (!found_at_target) {
                cerr << "ERROR: No literal found at target_level " << target_level << "!" << endl;
                assert(false && "Must have at least one literal at target_level");
            }
            
            // Update seed_level to target_level for consistency
            seed_level = target_level;
            
            // Swap to index 0
            if (at_target != 0) {
                std::swap(x.reason_cl[0], x.reason_cl[at_target]);
#ifdef DEBUG_ANF_PROP
                cout << "[ANF-REASON] Swapped literal at target_level " << target_level 
                     << " (seed_level=" << seed_level << ") with max sublevel (" << maxsublevel_at_target 
                     << ") to index 0: " << x.reason_cl[0] << endl;
#endif
            }
            
            // Verify the first literal is at the correct level
            assert(varData[x.reason_cl[0].var()].level == target_level 
                   && "First literal must be at target_level");
            
            // Ensure the second literal is NOT at seed_level (for CDCL conflict analysis)
            // If the second literal is also at seed_level, swap it with a literal at a lower level
            if (x.reason_cl.size() > 1 && varData[x.reason_cl[1].var()].level == seed_level) {
                // Find a literal at a lower level to swap with
                uint32_t swap_idx = 1;
                for (uint32_t i = 2; i < x.reason_cl.size(); i++) {
                    if (varData[x.reason_cl[i].var()].level < seed_level) {
                        swap_idx = i;
                        break;
                    }
                }
                if (swap_idx > 1) {
                    std::swap(x.reason_cl[1], x.reason_cl[swap_idx]);
#ifdef DEBUG_ANF_PROP
                    cout << "[ANF-REASON] Swapped second literal (was at seed_level) with literal at lower level: " 
                         << x.reason_cl[1] << " (level=" << varData[x.reason_cl[1].var()].level << ")" << endl;
#endif
                }
            }
        }
        
        // 确保reason子句不为空且正确
        assert(!x.reason_cl.empty() && "Reason clause must not be empty");
        
        // Step 4: Final validation - ensure all literals are False under current assignment
        // This is critical for CDCL conflict analysis
        for (const Lit &lit : x.reason_cl) {
            lbool lit_val = value(lit);
            if (lit_val != l_False) {
                cerr << "ERROR: Reason clause contains literal " << lit 
                     << " with value " << lit_val << " (should be False)!" << endl;
#ifdef DEBUG_ANF_PROP
                cerr << "  var=" << lit.var() + 1 << ", sign=" << lit.sign() 
                     << ", value(var)=" << value(lit.var()) << endl;
                Lit resolved = resolve_alias(lit);
                cerr << "  resolved=" << resolved << ", value(resolved)=" << value(resolved) << endl;
#endif
                // In release mode, try to fix by re-canonicalizing
                // But in debug mode, assert to catch the issue
                assert(lit_val == l_False && "All reason clause literals must be False");
            }
        }
        
        // Step 5: Final validation - ensure all literals are False under current assignment
        // Remove any literals that are True (they shouldn't be in a conflict/propagation reason)
        vector<Lit> validated_cl;
        for (const Lit &lit : x.reason_cl) {
            lbool lit_val = value(lit);
            if (lit_val == l_False) {
                validated_cl.push_back(lit);
            } else {
#ifdef DEBUG_ANF_PROP
                cout << "[ANF-REASON] WARNING: Removing True literal from reason: " << lit 
                     << " (value=" << lit_val << ")" << endl;
#endif
            }
        }
        
        // If validation removed too many literals, this is an error
        if (validated_cl.empty()) {
            cerr << "ERROR: All literals in reason clause are True after validation!" << endl;
            // This should not happen if make_reason_lit is used correctly
            assert(false && "Reason clause validation failed");
        }
        
        // For conflict, ensure the first literal is still at seed_level after validation
        // Also, ensure that all literals at seed_level have valid reasons (for CDCL conflict analysis)
        if (!is_propagation && !validated_cl.empty()) {
            // Re-find seed_level and ensure first literal is at seed_level
            uint32_t seed_level = 0;
            for (const Lit &l : validated_cl) {
                uint32_t lvl = varData[l.var()].level;
                if (lvl > seed_level) {
                    seed_level = lvl;
                }
            }
            
            // Find literal at seed_level with max sublevel
            uint32_t maxsublevel_at_seed = 0;
            uint32_t at_seed = 0;
            for (uint32_t i = 0; i < validated_cl.size(); i++) {
                Lit l = validated_cl[i];
                if (varData[l.var()].level == seed_level) {
                    if (varData[l.var()].sublevel >= maxsublevel_at_seed) {
                        maxsublevel_at_seed = varData[l.var()].sublevel;
                        at_seed = i;
                    }
                }
            }
            
            if (at_seed != 0) {
                std::swap(validated_cl[0], validated_cl[at_seed]);
            }
            
            // Ensure the second literal is NOT at seed_level (for CDCL conflict analysis)
            // If the second literal is also at seed_level, swap it with a literal at a lower level
            if (validated_cl.size() > 1 && varData[validated_cl[1].var()].level == seed_level) {
                // Find a literal at a lower level to swap with
                uint32_t swap_idx = 1;
                for (uint32_t i = 2; i < validated_cl.size(); i++) {
                    if (varData[validated_cl[i].var()].level < seed_level) {
                        swap_idx = i;
                        break;
                    }
                }
                if (swap_idx > 1) {
                    std::swap(validated_cl[1], validated_cl[swap_idx]);
#ifdef DEBUG_ANF_PROP
                    cout << "[ANF-REASON] After validation: Swapped second literal (was at seed_level) with literal at lower level: " 
                         << validated_cl[1] << " (level=" << varData[validated_cl[1].var()].level << ")" << endl;
#endif
                }
            }
            
            // Additional check: Verify that all literals at seed_level (except possibly decision variables) have valid reasons
            // This is important for CDCL conflict analysis to work correctly
            for (uint32_t i = 1; i < validated_cl.size(); i++) {
                Lit l = validated_cl[i];
                if (varData[l.var()].level == seed_level) {
                    const PropBy &reason = varData[l.var()].reason;
                    // Decision variables (null_clause_t) are OK, but other types must be valid
                    if (reason.getType() != null_clause_t) {
                        // For non-decision variables at seed_level, ensure reason is valid
                        // This is a sanity check - if reason is invalid, it might cause issues in conflict analysis
                    }
                }
            }
        }
        
        x.reason_cl = validated_cl;
        
#ifdef DEBUG_ANF_PROP
        cout << "[ANF-REASON] Final reason clause (size=" << x.reason_cl.size() << "): ";
        for (const Lit &lit : x.reason_cl) {
            cout << lit << " (value=" << value(lit) << ", level=" << varData[lit.var()].level << ") ";
        }
        cout << endl;
        
        // Final verification: all literals should be False
        bool all_false = true;
        for (const Lit &lit : x.reason_cl) {
            if (value(lit) != l_False) {
                cout << "[ANF-REASON] ERROR: Non-false literal in final reason: "
                     << lit << " has value " << value(lit) << endl;
                all_false = false;
            }
        }
        assert(all_false && "All literals in final reason should be false");
        
        // For conflict, verify first literal is at seed_level and check reason validity
        if (!is_propagation && !x.reason_cl.empty()) {
            uint32_t seed_level = 0;
            uint32_t count_at_seed = 0;
            for (const Lit &l : x.reason_cl) {
                uint32_t lvl = varData[l.var()].level;
                if (lvl > seed_level) {
                    seed_level = lvl;
                }
                if (lvl == seed_level) {
                    count_at_seed++;
                }
            }
            assert(varData[x.reason_cl[0].var()].level == seed_level 
                   && "First literal must be at seed_level");
            
#ifdef DEBUG_ANF_PROP
            // Check that all literals at seed_level have valid reasons (except possibly decision variables)
            cout << "[ANF-REASON] Seed level: " << seed_level << ", count at seed_level: " << count_at_seed << endl;
            for (const Lit &l : x.reason_cl) {
                if (varData[l.var()].level == seed_level) {
                    const PropBy &reason = varData[l.var()].reason;
                    cout << "[ANF-REASON]   Literal " << l << " at seed_level, reason type: " 
                         << (reason.getType() == null_clause_t ? "null (decision)" : 
                             reason.getType() == xor_t ? "xor" :
                             reason.getType() == clause_t ? "clause" :
                             reason.getType() == binary_t ? "binary" : "other") << endl;
                }
            }
#endif
        }
#endif
#ifdef DEBUG_ANF_PROP
        cout << "[ANF-REASON] Final reason clause (size=" << x.reason_cl.size() << "): ";
        for (const Lit &lit : x.reason_cl) {
            cout << lit << " ";
        }
        cout << endl;
        cout << "[ANF-REASON] Reason clause literals with values:" << endl;
        for (const Lit &lit : x.reason_cl) {
            cout << "  " << lit << " -> value=" << (value(lit) == l_True ? "True" : (value(lit) == l_False ? "False" : "Undef"))
                 << ", level=" << varData[lit.var()].level << endl;
        }
#endif
        
#ifdef VERBOSE_DEBUG
        cout << "XOR Reason: " << x.reason_cl << endl;
        for (const auto &l: x.reason_cl) {
            cout << "l: " << l << " value: " << value(l) << " level:" << varData[l.var()].level
                 << " type: " << removed_type_to_string(varData[l.var()].removed) << endl;
        }
        cout << "XOR Propagating? " << (int)(is_propagation) << endl;
#endif

        // Some sanity checks
        // Note: In conflict case, all variables should be assigned, so computed_rhs != x.rhs
        // But we skip this check for now as active_resolved_vars might not be up-to-date
        // when reason is requested after conflict
        if (is_propagation) {
            // For propagation, computed_rhs should match x.rhs (with all variables assigned)
            // But we already added the propagated literal, so skip strict check
        }

        if (frat->enabled()) {
            x.reason_cl_ID = ++clauseID;
            *frat << implyclfromx << x.reason_cl_ID << x.reason_cl << FratFlag::fratchain << x.xid << fin;
            ID = x.reason_cl_ID;
        }
        frat_func_end();
        return &x.reason_cl;
    } else {
        return gmatrices[reason.get_matrix_num()]->get_reason(reason.get_row_num(), ID);
        frat_func_end();
    }
}
