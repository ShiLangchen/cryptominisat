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

#include "xorextsimplifier.h"
#include "solver.h"

using namespace CMSat;

XorExtSimplifier::XorExtSimplifier(Solver* _solver)
    : solver(_solver)
{
}

XorExtSimplifier::~XorExtSimplifier()
{
}

int XorExtSimplifier::add_ext_substitution(
    uint32_t target,
    const vector<uint32_t>& factors)
{
    int idx = xor_ext_subs.size();
    xor_ext_subs.emplace_back(target, factors);
    
    for (uint32_t v : factors) {
        xor_ext_by_factor[v].push_back(idx);
    }
    
    return idx;
}

void XorExtSimplifier::set_tseitin_clauses(
    int sub_idx,
    const unordered_map<uint32_t, BinClauseInfo>& bin_infos,
    ClOffset all_true_cl_offset)
{
    if (sub_idx < 0 || sub_idx >= (int)xor_ext_subs.size()) {
        return;
    }
    
    xor_ext_subs[sub_idx].factor_bin_info = bin_infos;
    xor_ext_subs[sub_idx].all_true_cl_offset = all_true_cl_offset;
}

void XorExtSimplifier::handle_var_assignment(uint32_t v, bool value)
{
    auto it = xor_ext_by_factor.find(v);
    if (it == xor_ext_by_factor.end()) {
        return;
    }
    
    for (int sub_idx : it->second) {
        ExtSubstitution& sub = xor_ext_subs[sub_idx];
        
        if (sub.level >= 0) {
            continue;
        }
        
        if (sub.current_degree == 0) {
            continue;
        }
        
        if (!value) {
            sub.current_degree = 0;
            undo_stack.emplace_back(UndoAction::DEGREE_DEC, sub_idx, v);
        } else {
            update_degree(sub_idx, v);
        }
    }
}

bool XorExtSimplifier::update_degree(int sub_idx, uint32_t assigned_var)
{
    ExtSubstitution& sub = xor_ext_subs[sub_idx];
    
    if (sub.current_degree == 0) {
        return false;
    }
    
    sub.current_degree--;
    undo_stack.emplace_back(UndoAction::DEGREE_DEC, sub_idx, assigned_var);
    
    if (sub.current_degree == 1) {
        return true;
    }
    
    if (sub.current_degree == 0) {
        return true;
    }
    
    return false;
}

bool XorExtSimplifier::apply_substitution(int sub_idx)
{
    ExtSubstitution& sub = xor_ext_subs[sub_idx];
    
    if (sub.active) {
        return true;
    }
    
    sub.active = true;
    active_substitutions.push_back(sub_idx);
    undo_stack.emplace_back(UndoAction::ACTIVATE, sub_idx);
    
    return true;
}

bool XorExtSimplifier::propagate_substitutions()
{
    return true;
}

void XorExtSimplifier::backtrack(int new_level)
{
    if (undo_stack_levels.empty() || new_level >= (int)undo_stack_levels.size()) {
        return;
    }
    
    uint32_t target_undo_pos = undo_stack_levels[new_level];
    
    while (undo_stack.size() > target_undo_pos) {
        const UndoAction& action = undo_stack.back();
        
        switch (action.type) {
            case UndoAction::ACTIVATE: {
                ExtSubstitution& sub = xor_ext_subs[action.sub_idx];
                sub.active = false;
                sub.level = -1;
                
                auto it = std::find(active_substitutions.begin(),
                                  active_substitutions.end(),
                                  action.sub_idx);
                if (it != active_substitutions.end()) {
                    active_substitutions.erase(it);
                }
                break;
            }
            
            case UndoAction::DEGREE_DEC: {
                ExtSubstitution& sub = xor_ext_subs[action.sub_idx];
                sub.current_degree++;
                break;
            }
            
            case UndoAction::ALIAS_ADD: {
                gauss_alias.erase(action.var);
                break;
            }
        }
        
        undo_stack.pop_back();
    }
    
    undo_stack_levels.resize(new_level);
}

void XorExtSimplifier::clear()
{
    xor_ext_subs.clear();
    xor_ext_by_factor.clear();
    gauss_alias.clear();
    active_substitutions.clear();
    undo_stack.clear();
    undo_stack_levels.clear();
}

void XorExtSimplifier::deactivate_substitution(int sub_idx)
{
    ExtSubstitution& sub = xor_ext_subs[sub_idx];
    sub.active = false;
    sub.level = -1;
}

uint32_t XorExtSimplifier::get_remaining_factor(int sub_idx) const
{
    const ExtSubstitution& sub = xor_ext_subs[sub_idx];
    
    for (uint32_t f : sub.factors) {
        if (solver->value(f) == l_Undef) {
            return f;
        }
    }
    
    return var_Undef;
}

void XorExtSimplifier::set_substitution_level(int sub_idx, int level)
{
    if (sub_idx >= 0 && sub_idx < (int)xor_ext_subs.size()) {
        xor_ext_subs[sub_idx].level = level;
    }
}

const vector<int>* XorExtSimplifier::get_substitutions_for_var(uint32_t v) const
{
    auto it = xor_ext_by_factor.find(v);
    if (it == xor_ext_by_factor.end()) {
        return nullptr;
    }
    return &(it->second);
}

void XorExtSimplifier::set_gauss_alias(uint32_t target, uint32_t base)
{
    gauss_alias[target] = base;
}

void XorExtSimplifier::set_gauss_alias_direct(uint32_t target, uint32_t base)
{
    gauss_alias[target] = base;
}

void XorExtSimplifier::remove_gauss_alias(uint32_t target)
{
    gauss_alias.erase(target);
}

uint32_t XorExtSimplifier::get_gauss_alias(uint32_t var) const
{
    auto it = gauss_alias.find(var);
    if (it == gauss_alias.end()) {
        return var_Undef;
    }
    return it->second;
}
