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

#pragma once

#include "solvertypesmini.h"
#include "clauseallocator.h"
#include <vector>
#include <unordered_map>

namespace CMSat {

using std::vector;
using std::unordered_map;

class Solver;
class Clause;

struct BinClauseInfo {
    Lit lit;
    bool red;
    int32_t id;
    
    BinClauseInfo() : lit(lit_Undef), red(false), id(0) {}
    BinClauseInfo(Lit _lit, bool _red, int32_t _id) : lit(_lit), red(_red), id(_id) {}
};

struct ExtSubstitution {
    uint32_t target;
    vector<uint32_t> factors;
    uint32_t initial_degree;
    uint32_t current_degree;
    unordered_map<uint32_t, BinClauseInfo> factor_bin_info;
    ClOffset all_true_cl_offset;
    bool active;
    int level;
    
    ExtSubstitution()
        : target(var_Undef)
        , initial_degree(0)
        , current_degree(0)
        , all_true_cl_offset(CL_OFFSET_MAX)
        , active(false)
        , level(-1)
    {}
    
    ExtSubstitution(uint32_t _target, const vector<uint32_t>& _factors)
        : target(_target)
        , factors(_factors)
        , initial_degree(_factors.size())
        , current_degree(_factors.size())
        , all_true_cl_offset(CL_OFFSET_MAX)
        , active(false)
        , level(-1)
    {}
};

class XorExtSimplifier
{
public:
    XorExtSimplifier(Solver* _solver);
    ~XorExtSimplifier();
    
    int add_ext_substitution(
        uint32_t target,
        const vector<uint32_t>& factors
    );
    
    void set_tseitin_clauses(
        int sub_idx,
        const unordered_map<uint32_t, BinClauseInfo>& bin_infos,
        ClOffset all_true_cl_offset
    );
    
    bool propagate_substitutions();
    
    void backtrack(int new_level);
    
    void clear();
    
    size_t get_num_substitutions() const { 
        return xor_ext_subs.size(); 
    }
    
    const vector<ExtSubstitution>& get_substitutions() const {
        return xor_ext_subs;
    }
    
    void handle_var_assignment(uint32_t v, bool value);
    
    uint32_t get_remaining_factor(int sub_idx) const;
    
    void set_substitution_level(int sub_idx, int level);
    
    const vector<int>* get_substitutions_for_var(uint32_t v) const;
    
    void set_gauss_alias(uint32_t target, uint32_t base);
    
    void set_gauss_alias_direct(uint32_t target, uint32_t base);
    
    void remove_gauss_alias(uint32_t target);
    
    uint32_t get_gauss_alias(uint32_t var) const;
    
    vector<ExtSubstitution>& get_substitutions_mut() {
        return xor_ext_subs;
    }
    
private:
    Solver* solver;
    
    vector<ExtSubstitution> xor_ext_subs;
    
    unordered_map<uint32_t, vector<int>> xor_ext_by_factor;
    
    unordered_map<uint32_t, uint32_t> gauss_alias;
    
    vector<int> active_substitutions;
    
    struct UndoAction {
        enum Type { ACTIVATE, DEGREE_DEC, ALIAS_ADD };
        Type type;
        int sub_idx;
        uint32_t var;
        
        UndoAction(Type _type, int _idx, uint32_t _v = var_Undef)
            : type(_type), sub_idx(_idx), var(_v) {}
    };
    
    vector<UndoAction> undo_stack;
    vector<uint32_t> undo_stack_levels;
    
    bool apply_substitution(int sub_idx);
    void deactivate_substitution(int sub_idx);
    bool update_degree(int sub_idx, uint32_t assigned_var);
};

}
