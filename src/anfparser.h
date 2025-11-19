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

#include <string.h>
#include "streambuffer.h"
#include "solvertypesmini.h"
#include "anf_elimination.h"
#include <cstdlib>
#include <cmath>
#include <sstream>
#include <iostream>
#include <iomanip>
#include <vector>
#include <fstream>
#include <complex>
#include <cassert>
#include <unordered_map>

using std::vector;
using std::cout;
using std::endl;

namespace CMSat {

struct ANFProductTerm {
    vector<uint32_t> vars;
    uint32_t aux_var;
    vector<int32_t> binary_clause_ids;
    ANFProductTerm() : aux_var(var_Undef) {}
};

template <class C, class S>
class ANFParser
{
    public:
        ANFParser(S* solver, unsigned _verbosity);
        
        template <class T> bool parse_ANF(T input_stream);
        
    private:
        bool parse_ANF_main(C& in);
        bool parse_header(C& in);
        bool parse_and_add_anf_equation(C& in);
        bool parse_anf_term(C& in, ANFProductTerm& term, bool& is_constant);
        bool match(C& in, const char* str);
        bool check_var(const uint32_t var);
        uint32_t introduce_product_var(const vector<uint32_t>& product_vars);
        void add_product_cnf_clauses(uint32_t product_var, const vector<uint32_t>& vars);
        
        S* solver;
        unsigned verbosity;
        size_t lineNum;
        
        vector<Lit> lits;
        vector<uint32_t> xor_vars;
        
        size_t anf_equations_added;
        size_t cnf_clauses_added;
        uint32_t next_aux_var;
        
        struct VectorHash {
            size_t operator()(const vector<uint32_t>& v) const {
                size_t seed = v.size();
                for(auto& i : v) {
                    seed ^= i + 0x9e3779b9 + (seed << 6) + (seed >> 2);
                }
                return seed;
            }
        };
        std::unordered_map<vector<uint32_t>, uint32_t, VectorHash> product_cache;
        std::unordered_map<uint32_t, vector<int32_t>> tseitin_binary_ids;
};

template<class C, class S>
ANFParser<C, S>::ANFParser(
    S* _solver,
    unsigned _verbosity
):
    solver(_solver),
    verbosity(_verbosity),
    lineNum(0),
    anf_equations_added(0),
    cnf_clauses_added(0),
    next_aux_var(0)
{
}

template<class C, class S>
bool ANFParser<C, S>::check_var(const uint32_t var)
{
    if (var >= (1ULL<<28)) {
        std::cerr
        << "ERROR! "
        << "Variable requested is far too large: " << var + 1 << endl
        << "--> At line " << lineNum+1
        << endl;
        return false;
    }
    
    if (var >= solver->nVars()) {
        solver->new_vars(var - solver->nVars() + 1);
    }
    
    return true;
}

template<class C, class S>
bool ANFParser<C, S>::match(C& in, const char* str)
{
    for (; *str != 0; ++str, ++in)
        if (*str != *in)
            return false;
    return true;
}

template<class C, class S>
bool ANFParser<C, S>::parse_header(C& in)
{
    ++in;
    in.skipWhitespace();
    std::string str;
    in.parseString(str);
    if (str == "cnf") {
        int num_vars, num_eqs;
        if (!in.parseInt(num_vars, lineNum) || !in.parseInt(num_eqs, lineNum)) {
            return false;
        }
        if (verbosity) {
            cout << "c ANF header: " << num_vars << " variables, " << num_eqs << " equations" << endl;
        }
        if (num_vars > 0) {
            solver->new_vars(num_vars);
        }
    } else {
        std::cerr << "ERROR! Expected 'cnf' after 'p' at line " << lineNum+1 << endl;
        return false;
    }
    return true;
}

template<class C, class S>
uint32_t ANFParser<C, S>::introduce_product_var(const vector<uint32_t>& product_vars)
{
    vector<uint32_t> sorted_vars = product_vars;
    std::sort(sorted_vars.begin(), sorted_vars.end());
    
    auto it = product_cache.find(sorted_vars);
    if (it != product_cache.end()) {
        return it->second;
    }
    
    uint32_t new_var = solver->nVars();
    solver->new_vars(1);
    next_aux_var = new_var + 1;
    
    product_cache[sorted_vars] = new_var;
    
    if (verbosity >= 2) {
        cout << "c Introduced auxiliary variable y" << new_var + 1 << " for product: ";
        for (size_t i = 0; i < sorted_vars.size(); i++) {
            cout << "x" << sorted_vars[i] + 1;
            if (i + 1 < sorted_vars.size()) cout << "*";
        }
        cout << endl;
    }
    
    add_product_cnf_clauses(new_var, sorted_vars);
    
    return new_var;
}

template<class C, class S>
void ANFParser<C, S>::add_product_cnf_clauses(uint32_t product_var, const vector<uint32_t>& vars)
{
    if (verbosity >= 3) {
        cout << "c   Adding Tseitin CNF for y" << product_var+1 << " = ";
        for (size_t i = 0; i < vars.size(); i++) {
            cout << "x" << vars[i]+1;
            if (i + 1 < vars.size()) cout << " & ";
        }
        cout << endl;
    }
    
    for (uint32_t v : vars) {
        lits.clear();
        lits.push_back(Lit(product_var, true));
        lits.push_back(Lit(v, false));
        solver->add_clause(lits);
        cnf_clauses_added++;
    }
    
    lits.clear();
    lits.push_back(Lit(product_var, false));
    for (uint32_t v : vars) {
        lits.push_back(Lit(v, true));
    }
    solver->add_clause(lits);
    cnf_clauses_added++;
}

template<class C, class S>
bool ANFParser<C, S>::parse_anf_term(C& in, ANFProductTerm& term, bool& is_constant)
{
    in.skipWhitespace();
    
    if (*in == 'T' || *in == 't') {
        ++in;
        is_constant = true;
        term.vars.clear();
        return true;
    }
    
    if (*in == 'F' || *in == 'f') {
        ++in;
        is_constant = false;
        term.vars.clear();
        return true;
    }
    
    is_constant = false;
    
    if (*in == '.') {
        ++in;
        int32_t num_vars;
        if (!in.parseInt(num_vars, lineNum)) {
            std::cerr << "ERROR! Expected number after '.' at line " << lineNum+1 << endl;
            return false;
        }
        
        if (num_vars < 0) {
            std::cerr << "ERROR! Number of variables cannot be negative at line " << lineNum+1 << endl;
            return false;
        }
        
        term.vars.clear();
        for (int32_t i = 0; i < num_vars; i++) {
            in.skipWhitespace();
            int32_t parsed_var;
            if (!in.parseInt(parsed_var, lineNum)) {
                std::cerr << "ERROR! Failed to parse variable " << i+1 << " of product term at line " << lineNum+1 << endl;
                return false;
            }
            
            if (parsed_var <= 0) {
                std::cerr << "ERROR! Variable must be positive in product term at line " << lineNum+1 << endl;
                return false;
            }
            
            uint32_t var = parsed_var - 1;
            if (!check_var(var)) {
                return false;
            }
            term.vars.push_back(var);
        }
    } else {
        int32_t parsed_var;
        if (!in.parseInt(parsed_var, lineNum)) {
            return false;
        }
        
        if (parsed_var <= 0) {
            std::cerr << "ERROR! Variable must be positive at line " << lineNum+1 << endl;
            return false;
        }
        
        uint32_t var = parsed_var - 1;
        if (!check_var(var)) {
            return false;
        }
        term.vars.clear();
        term.vars.push_back(var);
    }
    
    return true;
}

template<class C, class S>
bool ANFParser<C, S>::parse_and_add_anf_equation(C& in)
{
    if (!match(in, "x ")) {
        std::cerr << "ERROR! ANF equation must start with 'x ' at line " << lineNum+1 << endl;
        return false;
    }
    
    vector<ANFProductTerm> terms;
    bool rhs = true;
    
    for (;;) {
        in.skipWhitespace();
        
        if (*in == '0') {
            ++in;
            break;
        }
        
        ANFProductTerm term;
        bool is_constant;
        if (!parse_anf_term(in, term, is_constant)) {
            return false;
        }
        
        if (is_constant) {
            rhs ^= true;
        } else if (!term.vars.empty()) {
            terms.push_back(term);
        }
    }
    
    xor_vars.clear();
    
    for (auto& term : terms) {
        if (term.vars.size() == 1) {
            xor_vars.push_back(term.vars[0]);
        } else if (term.vars.size() > 1) {
            uint32_t aux_var = introduce_product_var(term.vars);
            xor_vars.push_back(aux_var);
        }
    }
    
    if (verbosity >= 2) {
        cout << "c   XOR clause: ";
        for (auto v : xor_vars) cout << v+1 << " ";
        cout << " = " << (rhs ? "1" : "0") << endl;
    }
    
    if (!xor_vars.empty()) {
        solver->add_xor_clause(xor_vars, rhs);
    } else if (rhs) {
        if (verbosity >= 2) {
            cout << "c   Adding empty clause (UNSAT)" << endl;
        }
        lits.clear();
        solver->add_clause(lits);
    }
    
    anf_equations_added++;
    
    in.skipWhitespace();
    if (!in.skipEOL(lineNum)) {
        return false;
    }
    lineNum++;
    
    return true;
}

template<class C, class S>
bool ANFParser<C, S>::parse_ANF_main(C& in)
{
    for (;;) {
        in.skipWhitespace();
        // todo：cnf_parse
        switch (*in) {
        case EOF:
            return true;
        case 'p':
            if (!parse_header(in)) {
                return false;
            }
            in.skipLine();
            lineNum++;
            break;
        case 'c':
            in.skipLine();
            lineNum++;
            break;
        case 'x':
            if (!parse_and_add_anf_equation(in)) {
                return false;
            }
            break;
        case '\n':
            in.skipLine();
            lineNum++;
            break;
        default:
            std::cerr << "ERROR! Unexpected character '" << *in 
                     << "' at line " << lineNum+1 << endl;
            return false;
        }
    }
    
    return true;
}

template <class C, class S>
template <class T>
bool ANFParser<C, S>::parse_ANF(T input_stream)
{
    const uint32_t origNumVars = solver->nVars();
    
    C in(input_stream);
    if (!parse_ANF_main(in)) {
        return false;
    }
    
    if (verbosity) {
        cout
        << "c -- ANF equations parsed: " << anf_equations_added << endl
        << "c -- CNF clauses added: " << cnf_clauses_added << endl
        << "c -- vars added (including auxiliary): " << (solver->nVars() - origNumVars)
        << endl;
        
    }
    
    return true;
}

}


