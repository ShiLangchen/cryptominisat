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
#include <unordered_set>

namespace CMSat {

using std::vector;
using std::unordered_map;
using std::unordered_set;

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
    int activated_level;
    int last_touch_level;
    vector<uint32_t> used_factors;
    
    ExtSubstitution()
        : target(var_Undef)
        , initial_degree(0)
        , current_degree(0)
        , all_true_cl_offset(CL_OFFSET_MAX)
        , active(false)
        , activated_level(-1)
        , last_touch_level(-1)
    {}
    
    ExtSubstitution(uint32_t _target, const vector<uint32_t>& _factors)
        : target(_target)
        , factors(_factors)
        , initial_degree(_factors.size())
        , current_degree(_factors.size())
        , all_true_cl_offset(CL_OFFSET_MAX)
        , active(false)
        , activated_level(-1)
        , last_touch_level(-1)
    {}
};

struct AliasUndo {
    uint32_t var;
    uint32_t old_alias;
    
    AliasUndo(uint32_t _var, uint32_t _old) : var(_var), old_alias(_old) {}
};

struct UndoEntry {
    enum Type {
        ALIAS_UNDO,
        ACTIVATE_SUBST,
        DEGREE_DEC
    };
    
    Type type;
    union {
        AliasUndo alias_undo;
        struct {
            int sub_idx;
        } activate_subst;
        struct {
            int sub_idx;
            uint32_t var;
        } degree_dec;
    };
    
    UndoEntry() : type(ALIAS_UNDO) {}
    UndoEntry(const AliasUndo& au) : type(ALIAS_UNDO), alias_undo(au) {}
    UndoEntry(Type t, int idx) : type(t) {
        if (t == ACTIVATE_SUBST) {
            activate_subst.sub_idx = idx;
        }
    }
    UndoEntry(Type t, int idx, uint32_t v) : type(t) {
        if (t == DEGREE_DEC) {
            degree_dec.sub_idx = idx;
            degree_dec.var = v;
        }
    }
};

class ANFElimination
{
public:
    ANFElimination(Solver* _solver);
    ~ANFElimination();
    
    int add_ext_substitution(
        uint32_t target,
        const vector<uint32_t>& factors
    );
    
    void set_tseitin_clauses(
        int sub_idx,
        const unordered_map<uint32_t, BinClauseInfo>& bin_infos,
        ClOffset all_true_cl_offset
    );
    
    void on_assignment(uint32_t v);
    
    bool propagate();
    
    void backtrack(int new_level);
    
    void clear();
    
    size_t get_num_substitutions() const { 
        return anf_subs.size(); 
    }
    
    const vector<ExtSubstitution>& get_substitutions() const {
        return anf_subs;
    }
    
    uint32_t resolve_alias(uint32_t v) const;
    
    void set_alias(uint32_t target, uint32_t rep);
    
    uint32_t get_alias(uint32_t var) const;
    
    bool is_alias_set(uint32_t var) const;
    
    const vector<int>* get_substitutions_for_var(uint32_t v) const;
    
    vector<ExtSubstitution>& get_substitutions_mut() {
        return anf_subs;
    }
    
    int current_decision_level() const;
    
    void update_undo_stack_level();
    
private:
    Solver* solver;
    
    vector<ExtSubstitution> anf_subs;
    
    unordered_map<uint32_t, vector<int>> anf_by_factor;
    
    unordered_map<uint32_t, uint32_t> alias;
    
    unordered_set<int> pending_set;
    
    vector<UndoEntry> undo_stack;
    vector<size_t> undo_stack_levels;
    
    enum EvalResult {
        VARIABLE,
        MULTIVARIATE,
        ZERO,
        ONE
    };
    
    EvalResult evaluate_monomial(int sub_idx, uint32_t& out_var);
    
    void push_undo_alias(uint32_t var, uint32_t old_alias);
    
    void push_undo_activate_subst(int sub_idx);
    
    void push_undo_degree_dec(int sub_idx, uint32_t var);
    
    void mark_pending(int sub_idx);
    
    void unmark_pending(int sub_idx);
};

}

