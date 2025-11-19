/******************************************
Copyright (C) 2025 ANF Extension for CryptoMiniSat

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

#include "anf_elimination.h"
#include "solver.h"

using namespace CMSat;

ANFElimination::ANFElimination(Solver* _solver)
    : solver(_solver)
{
}

ANFElimination::~ANFElimination()
{
}

int ANFElimination::add_ext_substitution(
    uint32_t target,
    const vector<uint32_t>& factors)
{
    int idx = anf_subs.size();
    anf_subs.emplace_back(target, factors);
    
    for (uint32_t v : factors) {
        anf_by_factor[v].push_back(idx);
    }
    
    return idx;
}

void ANFElimination::set_tseitin_clauses(
    int sub_idx,
    const unordered_map<uint32_t, BinClauseInfo>& bin_infos,
    ClOffset all_true_cl_offset)
{
    if (sub_idx < 0 || sub_idx >= (int)anf_subs.size()) {
        return;
    }
    
    anf_subs[sub_idx].factor_bin_info = bin_infos;
    anf_subs[sub_idx].all_true_cl_offset = all_true_cl_offset;
}

void ANFElimination::on_assignment(uint32_t v)
{
    auto it = anf_by_factor.find(v);
    if (it == anf_by_factor.end()) {
        return;
    }
    
    for (int sub_idx : it->second) {
        ExtSubstitution& sub = anf_subs[sub_idx];
        
        if (sub.active) {
            continue;
        }
        
        if (sub.current_degree == 0) {
            continue;
        }
        
        sub.last_touch_level = current_decision_level();
        mark_pending(sub_idx);
    }
}

bool ANFElimination::propagate()
{
    while (!pending_set.empty()) {
        auto it = pending_set.begin();
        int sub_idx = *it;
        pending_set.erase(it);
        
        ExtSubstitution& sub = anf_subs[sub_idx];
        
        if (sub.active) {
            continue;
        }
        
        uint32_t rep_var;
        EvalResult result = evaluate_monomial(sub_idx, rep_var);
        
        if (result == VARIABLE) {
            sub.active = true;
            sub.activated_level = current_decision_level();
            
            sub.used_factors.clear();
            for (uint32_t f : sub.factors) {
                uint32_t canon_f = resolve_alias(f);
                if (solver->value(canon_f) == l_True) {
                    sub.used_factors.push_back(canon_f);
                }
            }
            
            push_undo_activate_subst(sub_idx);
            
            uint32_t old_alias = get_alias(sub.target);
            push_undo_alias(sub.target, old_alias);
            alias[sub.target] = rep_var;
        } else if (result == MULTIVARIATE) {
            continue;
        }
    }
    
    return true;
}

ANFElimination::EvalResult ANFElimination::evaluate_monomial(int sub_idx, uint32_t& out_var)
{
    const ExtSubstitution& sub = anf_subs[sub_idx];
    
    vector<uint32_t> alive;
    
    for (uint32_t f : sub.factors) {
        uint32_t canon_f = resolve_alias(f);
        lbool val = solver->value(canon_f);
        
        if (val == l_Undef) {
            alive.push_back(canon_f);
        } else if (val == l_False) {
            return ZERO;
        }
    }
    
    if (alive.size() == 0) {
        return ONE;
    } else if (alive.size() == 1) {
        out_var = alive[0];
        return VARIABLE;
    } else {
        return MULTIVARIATE;
    }
}

uint32_t ANFElimination::resolve_alias(uint32_t v) const
{
    uint32_t curr = v;
    unordered_set<uint32_t> visited;
    
    while (true) {
        auto it = alias.find(curr);
        if (it == alias.end()) {
            return curr;
        }
        
        if (visited.count(curr)) {
            return curr;
        }
        visited.insert(curr);
        
        curr = it->second;
    }
}

void ANFElimination::set_alias(uint32_t target, uint32_t rep)
{
    uint32_t old = get_alias(target);
    push_undo_alias(target, old);
    if (rep == var_Undef) {
        alias.erase(target);
    } else {
        alias[target] = rep;
    }
}

uint32_t ANFElimination::get_alias(uint32_t var) const
{
    auto it = alias.find(var);
    if (it == alias.end()) {
        return var_Undef;
    }
    return it->second;
}

bool ANFElimination::is_alias_set(uint32_t var) const
{
    return alias.find(var) != alias.end();
}

void ANFElimination::backtrack(int new_level)
{
    if (undo_stack_levels.empty() || new_level >= (int)undo_stack_levels.size()) {
        return;
    }
    
    size_t target_undo_pos = undo_stack_levels[new_level];
    
    while (undo_stack.size() > target_undo_pos) {
        const UndoEntry& entry = undo_stack.back();
        
        switch (entry.type) {
            case UndoEntry::ALIAS_UNDO: {
                const AliasUndo& au = entry.alias_undo;
                auto it = alias.find(au.var);
                if (it != alias.end()) {
                    if (au.old_alias == var_Undef) {
                        alias.erase(it);
                    } else {
                        it->second = au.old_alias;
                    }
                } else if (au.old_alias != var_Undef) {
                    alias[au.var] = au.old_alias;
                }
                break;
            }
            
            case UndoEntry::ACTIVATE_SUBST: {
                ExtSubstitution& sub = anf_subs[entry.activate_subst.sub_idx];
                sub.active = false;
                sub.activated_level = -1;
                sub.used_factors.clear();
                unmark_pending(entry.activate_subst.sub_idx);
                break;
            }
            
            case UndoEntry::DEGREE_DEC: {
                ExtSubstitution& sub = anf_subs[entry.degree_dec.sub_idx];
                sub.current_degree++;
                break;
            }
        }
        
        undo_stack.pop_back();
    }
    
    undo_stack_levels.resize(new_level);
}

void ANFElimination::clear()
{
    anf_subs.clear();
    anf_by_factor.clear();
    alias.clear();
    pending_set.clear();
    undo_stack.clear();
    undo_stack_levels.clear();
}

const vector<int>* ANFElimination::get_substitutions_for_var(uint32_t v) const
{
    auto it = anf_by_factor.find(v);
    if (it == anf_by_factor.end()) {
        return nullptr;
    }
    return &(it->second);
}

int ANFElimination::current_decision_level() const
{
    return solver->decisionLevel();
}

void ANFElimination::update_undo_stack_level()
{
    int level = current_decision_level();
    while ((int)undo_stack_levels.size() <= level) {
        undo_stack_levels.push_back(undo_stack.size());
    }
    undo_stack_levels[level] = undo_stack.size();
}

void ANFElimination::push_undo_alias(uint32_t var, uint32_t old_alias)
{
    update_undo_stack_level();
    undo_stack.emplace_back(AliasUndo(var, old_alias));
}

void ANFElimination::push_undo_activate_subst(int sub_idx)
{
    update_undo_stack_level();
    undo_stack.emplace_back(UndoEntry::ACTIVATE_SUBST, sub_idx);
}

void ANFElimination::push_undo_degree_dec(int sub_idx, uint32_t var)
{
    update_undo_stack_level();
    undo_stack.emplace_back(UndoEntry::DEGREE_DEC, sub_idx, var);
}

void ANFElimination::mark_pending(int sub_idx)
{
    pending_set.insert(sub_idx);
}

void ANFElimination::unmark_pending(int sub_idx)
{
    pending_set.erase(sub_idx);
}

