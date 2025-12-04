#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include "solver.h"
#include "streambuffer.h"
#include "solvertypesmini.h"
#include <cstdlib>
#include <cmath>
#include <map>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <cassert>
#include <zlib.h>

namespace CMSat
{
// Move using declarations inside namespace to avoid global namespace pollution
using std::vector;
using std::string;
using std::cerr;
using std::cout;
using std::endl;
using std::map;
using std::unique_ptr;

template<class C, class S> class AnfParser
{
  public:
    AnfParser(S *solver, unsigned _verbosity);

    bool parse_ANF(const string &file_name, const bool strict_header, uint32_t offset_vars = 0);
    uint64_t max_var = numeric_limits<uint64_t>::max();
    const std::string dimacs_spec = "https://github.com/mtrimoska/WDSat/blob/master/README.md";
    const std::string please_read_dimacs =
            "\nPlease read ANF specification at https://github.com/mtrimoska/WDSat/blob/master/README.md";

  private:
    bool parse_ANF_main(C &in);
    bool read_clause(C &in);
    bool parse_and_add_clause(C &in);
    bool parse_and_add_xor_clause(C &in);
    bool parse_and_add_anf_clause(C &in);
    bool parse_header(C &in);

    bool scan_instance(C &in);
    bool scan_anf_clauses(C &in);
    bool read_anf_clause(C &in);

    bool check_var(const uint32_t var);

    S *solver;
    unsigned verbosity;

    //Stat
    size_t line_num = 1;

    //check header strictly
    bool strict_header = false;
    bool header_found = false;
    int num_header_vars = 0;
    int num_header_cls = 0;
    uint32_t offset_vars = 0;

    //Reduce temp overhead
    vector<Lit> lits;
    vector<vector<Lit>> poly;
    std::set<vector<Lit>> monos;
    std::vector<vector<Lit>> monos_vec;

    size_t norm_clauses_added = 0;
    size_t xor_clauses_added = 0;
    size_t eq_clauses_added = 0;
};


template<class C, class S>
AnfParser<C, S>::AnfParser(S *_solver, unsigned _verbosity) : solver(_solver), verbosity(_verbosity)
{
}

template<class C, class S> bool AnfParser<C, S>::check_var(const uint32_t var)
{
    if (var > max_var) {
        std::cerr << "ERROR! "
                  << "Variable requested is too large for DIMACS parser parameter: " << var << endl
                  << "--> At line " << line_num << please_read_dimacs << endl;
        return false;
    }

    if (var >= (1ULL << 28)) {
        std::cerr << "ERROR! "
                  << "Variable requested is far too large: " << var + 1 << endl
                  << "--> At line " << line_num << please_read_dimacs << endl;
        return false;
    }

    if ((int)var >= num_header_vars && strict_header) {
        std::cerr << "ERROR! "
                  << "Variable requested is larger than the header told us." << endl
                  << " -> var is : " << var + 1 << endl
                  << " -> header told us maximum will be : " << num_header_vars << endl
                  << " -> At line " << line_num << endl;
        return false;
    }

    if (var >= solver->nVars()) {
        assert(!strict_header);
        solver->new_vars(var - solver->nVars() + 1);
    }

    return true;
}

template<class C, class S> bool AnfParser<C, S>::read_clause(C &in)
{
    int32_t parsed_lit;
    uint32_t var;
    for (;;) {
        if (!in.parseInt(parsed_lit, line_num)) {
            return false;
        }
        if (parsed_lit == 0) {
            break;
        }

        var = std::abs(parsed_lit) - 1;
        var += offset_vars;

        if (!check_var(var)) {
            return false;
        }

        lits.push_back((parsed_lit > 0) ? Lit(var, false) : Lit(var, true));
        if (*in != ' ') {
            std::cerr << "ERROR! "
                      << "After last element on the line must be 0" << endl
                      << "--> At line " << line_num << please_read_dimacs << endl
                      << endl;
            return false;
        }
    }

    return true;
}

template<class C, class S> bool AnfParser<C, S>::scan_instance(C &in)
{
    std::string str;
    for (;;) {
        in.skipWhitespace();
        switch (*in) {
            case EOF:
                goto ARRANGE_IMPLICATIONS;
            case 'p':
                if (!parse_header(in)) {
                    return false;
                }
                in.skipLine();
                line_num++;
                break;
            case '\n':
                if (verbosity) {
                    cout << "c WARNING: Empty line at line number " << line_num
                         << " -- this is not part of the ANF specifications (" << dimacs_spec << "). Ignoring." << endl;
                }
                in.skipLine();
                line_num++;
                break;
            case 'x':
                ++in;
                scan_anf_clauses(in);
                break;
            case 'c':
                // Comment line - skip it during scanning
                in.skipLine();
                line_num++;
                break;
            default:
                // During scanning phase, we only expect 'x' lines (ANF clauses)
                // Other lines (CNF clauses, etc.) will be handled in parse_ANF_main
                // Skip unexpected characters during scan phase
                if (verbosity >= 2) {
                    cout << "c [SCAN] Line " << line_num << ": Skipping non-ANF line during scan phase" << endl;
                }
                in.skipLine();
                line_num++;
                break;
        }
    }
ARRANGE_IMPLICATIONS:
    for (const auto &mono: monos) {
        monos_vec.push_back(mono);
    }
    assert(std::is_sorted(monos_vec.begin(), monos_vec.end()));

    auto auxiliary_var_start = solver->nVars();
    solver->set_real_var_num(auxiliary_var_start);

    if (verbosity >= 2) {
        cout << "c [ANF] Found " << monos_vec.size() << " unique product terms (monomials)" << endl;
    }

    solver->new_vars(monos_vec.size());

    assert(solver->nVars() == auxiliary_var_start + monos_vec.size());

    size_t mono_idx = 0;
    for (const auto &mono: monos_vec) {
        Lit aux_lit = Lit(auxiliary_var_start++, false);
        const size_t mono_size = mono.size();
        // aux_lit <-> (mono[0] & mono[1] & ... )
        // which is equivalent to:
        // (!aux_lit v mono[0]) & (!aux_lit v mono[1]) & ... & (!aux_lit v mono[mono_size - 1]) & (aux_lit v !mono[0] v !mono[1] v ... v !mono[mono_size - 1])

        if (verbosity >= 3) {
            cout << "c [ANF] Monomial " << mono_idx << ": y_" << aux_lit.var() + 1 
                 << " = ";
            for (size_t i = 0; i < mono_size; i++) {
                if (i > 0) cout << " & ";
                cout << "x_" << mono[i].var() + 1;
                if (mono[i].sign()) cout << "'";
            }
            cout << endl;
        }

        // add clauses
        for (auto lit: mono) {
            norm_clauses_added++;
            solver->add_clause({~aux_lit, lit});
        }

        vector<Lit> cls;
        cls.reserve(mono_size + 1);
        cls.push_back(aux_lit);
        for (auto lit: mono) {
            cls.push_back(~lit);
        }
        norm_clauses_added++;
        solver->add_clause(cls);

        // add equivalence
        eq_clauses_added++;
        solver->add_eq_clause(mono, aux_lit);
        mono_idx++;
    }

    if (verbosity >= 2) {
        cout << "c [ANF] Created " << monos_vec.size() << " auxiliary variables ("
             << auxiliary_var_start - monos_vec.size() << " to " << auxiliary_var_start - 1 << ")" << endl;
    }
    return true;
}

template<class C, class S> bool AnfParser<C, S>::scan_anf_clauses(C &in)
{
    poly.clear();
    if (!read_anf_clause(in)) {
        return false;
    }
    if (!in.skipEOL(line_num)) {
        return false;
    }
    line_num++;

    size_t new_monos = 0;
    for (auto &mono: poly) {
        if (mono.size() <= 1) continue;
        std::sort(mono.begin(), mono.end());
        auto result = monos.insert(mono);
        if (result.second) {
            new_monos++;
            if (verbosity >= 3) {
                cout << "c [SCAN] Line " << line_num - 1 << ": Found new product term: ";
                for (size_t i = 0; i < mono.size(); i++) {
                    if (i > 0) cout << " & ";
                    cout << "x_" << mono[i].var() + 1;
                    if (mono[i].sign()) cout << "'";
                }
                cout << endl;
            }
        }
    }

    if (verbosity >= 2 && new_monos > 0) {
        cout << "c [SCAN] Line " << line_num - 1 << ": Added " << new_monos 
             << " new product term(s), total unique: " << monos.size() << endl;
    }

    return true;
}

template<class C, class S> bool AnfParser<C, S>::read_anf_clause(C &in)
{
    int32_t parsed_lit;
    uint32_t var;
    std::string str;
    for (;;) {
        in.parseString(str);

        bool with_unit_mono = false;
        switch (str[0]) {
            case '0':
                return true;
            case 'T': {
                with_unit_mono = !with_unit_mono;
                break;
            }
            case '.': {
                size_t mono_size = std::stoull(str.substr(1));
                vector<Lit> mono;
                for (size_t i = 0; i < mono_size; i++) {
                    if (!in.parseInt(parsed_lit, line_num)) return false;
                    var = std::abs(parsed_lit) - 1;
                    var += offset_vars;
                    if (!check_var(var)) return false;
                    mono.push_back((parsed_lit > 0) ? Lit(var, false) : Lit(var, true));
                }
                poly.push_back(mono);
                break;
            }
            default: {
                parsed_lit = std::stoi(str);
                vector<Lit> mono;
                var = std::abs(parsed_lit) - 1;
                var += offset_vars;
                if (!check_var(var)) return false;
                mono.push_back((parsed_lit > 0) ? Lit(var, false) : Lit(var, true));
                poly.push_back(mono);
                break;
            }
        }

        if (with_unit_mono) poly.push_back({});
    }
    return true;
}

template<class C, class S> bool AnfParser<C, S>::parse_header(C &in)
{
    ++in;
    in.skipWhitespace();
    std::string str;
    in.parseString(str);
    if (str == "cnf") {
        if (header_found && strict_header) {
            std::cerr << "ERROR: CNF header ('p cnf vars cls') found twice in file! Exiting." << endl;
            exit(-1);
        }
        header_found = true;

        if (!in.parseInt(num_header_vars, line_num) || !in.parseInt(num_header_cls, line_num)) {
            return false;
        }
        if (verbosity) {
            cout << "c o -- header says num vars:   " << std::setw(12) << num_header_vars << endl;
            cout << "c o -- header says num clauses:" << std::setw(12) << num_header_cls << endl;
        }
        if (num_header_vars < 0) {
            std::cerr << "ERROR: Number of variables in header cannot be less than 0" << endl;
            return false;
        }
        if (num_header_cls < 0) {
            std::cerr << "ERROR: Number of clauses in header cannot be less than 0" << endl;
            return false;
        }
        num_header_vars += offset_vars;

        if (solver->nVars() < (size_t)num_header_vars) {
            solver->new_vars(num_header_vars - solver->nVars());
        }
    } else {
        std::cerr << "PARSE ERROR! Unexpected char (hex: " << std::hex << std::setw(2) << std::setfill('0') << "0x"
                  << *in << std::setfill(' ') << std::dec << ")"
                  << " At line " << line_num << "' in the header" << please_read_dimacs << endl;
        return false;
    }

    return true;
}

template<class C, class S> bool AnfParser<C, S>::parse_and_add_clause(C &in)
{
    lits.clear();
    if (!read_clause(in)) {
        return false;
    }
    in.skipWhitespace();
    if (!in.skipEOL(line_num)) {
        return false;
    }
    line_num++;
    
    if (verbosity >= 3) {
        cout << "c [CNF] Line " << line_num - 1 << ": Adding CNF clause: ";
        for (size_t i = 0; i < lits.size(); i++) {
            if (i > 0) cout << " ";
            if (lits[i].sign()) cout << "-";
            cout << lits[i].var() + 1;
        }
        cout << " 0" << endl;
    }
    
    solver->add_clause(lits);
    norm_clauses_added++;
    return true;
}

template<class C, class S> bool AnfParser<C, S>::parse_and_add_xor_clause(C &in)
{
    lits.clear();
    if (!read_clause(in)) {
        return false;
    }
    if (!in.skipEOL(line_num)) {
        return false;
    }
    line_num++;
    solver->add_xor_clause(lits, true);
    xor_clauses_added++;
    return true;
}

template<class C, class S> bool AnfParser<C, S>::parse_and_add_anf_clause(C &in)
{
    poly.clear();
    if (!read_anf_clause(in)) {
        return false;
    }
    if (!in.skipEOL(line_num)) {
        return false;
    }
    line_num++;

    // now add the anf clause. Monomials(degree >= 2) will be replaced by corresponding auxiliary variables
    lits.clear();
    bool with_unit_mono = false;
    
    if (verbosity >= 3) {
        cout << "c [ANF] Line " << line_num - 1 << ": Parsing ANF clause:" << endl;
        cout << "c [ANF]   Original terms: ";
        for (size_t i = 0; i < poly.size(); i++) {
            if (i > 0) cout << " XOR ";
            if (poly[i].size() == 0) {
                cout << "1";
            } else if (poly[i].size() == 1) {
                cout << "x_" << poly[i][0].var() + 1;
                if (poly[i][0].sign()) cout << "'";
            } else {
                cout << "(";
                for (size_t j = 0; j < poly[i].size(); j++) {
                    if (j > 0) cout << " & ";
                    cout << "x_" << poly[i][j].var() + 1;
                    if (poly[i][j].sign()) cout << "'";
                }
                cout << ")";
            }
        }
        cout << endl;
    }
    
    for (const auto &mono: poly) {
        switch (mono.size()) {
            case 0: {
                with_unit_mono = !with_unit_mono;
                break;
            }
            case 1: {
                lits.push_back(mono[0]);
                break;
            }
            default: {
                // find auxiliary variable for this monomial
                auto iter = std::lower_bound(monos_vec.begin(), monos_vec.end(), mono);
                assert(iter != monos_vec.end() && (*iter) == mono);

                size_t index = std::distance(monos_vec.begin(), iter);
                Lit aux_lit = Lit(solver->nVars() - monos_vec.size() + index, false);

                lits.push_back(aux_lit);
                break;
            }
        }
    }

    bool rhs = !with_unit_mono;
    
    if (verbosity >= 3) {
        cout << "c [ANF]   Converted to XOR clause: ";
        for (size_t i = 0; i < lits.size(); i++) {
            if (i > 0) cout << " XOR ";
            if (lits[i].var() >= solver->nVars() - monos_vec.size()) {
                // This is an auxiliary variable
                cout << "y_" << lits[i].var() + 1;
            } else {
                cout << "x_" << lits[i].var() + 1;
            }
            if (lits[i].sign()) cout << "'";
        }
        cout << " = " << (rhs ? "1" : "0") << endl;
    }

    solver->add_xor_clause(lits, rhs);
    xor_clauses_added++;
    return true;
}

template<class C, class S> bool AnfParser<C, S>::parse_ANF_main(C &in)
{
    std::string str;
    for (;;) {
        in.skipWhitespace();
        char c = *in;
        
        // Check for EOF first
        if (c == EOF) {
            return true;
        }
        
        // Check if it's a CNF clause (starts with digit or minus sign)
        // CNF clauses start with a literal (digit or '-' followed by digit)
        if ((c >= '0' && c <= '9') || c == '-') {
            if (verbosity >= 3) {
                cout << "c [PARSE] Line " << line_num << ": CNF clause detected" << endl;
            }
            // Try to parse as CNF clause
            // read_clause will handle the parsing and return false if it fails
            if (!parse_and_add_clause(in)) {
                // If parsing failed, it might not be a CNF clause
                // Check if it's actually an ANF clause or other format
                // For now, we'll let the error propagate up
                return false;
            }
            continue;
        }
        
        // Handle other cases with switch
        switch (c) {
            case 'p':
                if (verbosity >= 3) {
                    cout << "c [PARSE] Line " << line_num << ": Header line (skipping)" << endl;
                }
                in.skipLine();
                line_num++;
                break;
            case 'x':
                if (verbosity >= 3) {
                    cout << "c [PARSE] Line " << line_num << ": ANF clause detected" << endl;
                }
                ++in;
                if (!parse_and_add_anf_clause(in)) return false;
                break;
            case 'c':
                // Comment line - skip it
                if (verbosity >= 3) {
                    cout << "c [PARSE] Line " << line_num << ": Comment line" << endl;
                }
                in.skipLine();
                line_num++;
                break;
            case '\n':
                if (verbosity) {
                    cout << "c WARNING: Empty line at line number " << line_num
                         << " -- this is not part of the ANF specifications (" << dimacs_spec << "). Ignoring." << endl;
                }
                in.skipLine();
                line_num++;
                break;
            default:
                // Unknown character - could be an error or we should skip
                if (verbosity) {
                    cout << "c WARNING: Unexpected character '" << c 
                         << "' (hex: 0x" << std::hex << (int)(unsigned char)c << std::dec
                         << ") at line " << line_num << ". Skipping line." << endl;
                }
                in.skipLine();
                line_num++;
                break;
        }
    }

    return true;
}


template<class C, class S>
bool AnfParser<C, S>::parse_ANF(const string &file_name, const bool _strict_header, uint32_t _offset_vars)
{
    strict_header = _strict_header;
    offset_vars = _offset_vars;
    const uint32_t origNumVars = solver->nVars();

    gzFile gzf1 = gzopen(file_name.c_str(), "rb");
    C in1(gzf1);
    // add eq clauses (including those cnf clauses)
    if (!scan_instance(in1)) return false;
    gzclose(gzf1);

    gzFile gzf2 = gzopen(file_name.c_str(), "rb");
    C in2(gzf2);
    // add xor clauses
    if (!parse_ANF_main(in2)) return false;
    gzclose(gzf2);

    if (verbosity >= 1) {
        cout << "c ========== ANF Parsing Summary ==========" << endl;
        cout << "c Normal CNF clauses added: " << norm_clauses_added << endl;
        cout << "c XOR clauses added: " << xor_clauses_added << endl;
        cout << "c Equivalence clauses added: " << eq_clauses_added << endl;
        cout << "c Total variables added: " << (solver->nVars() - origNumVars) << endl;
        cout << "c   - Original variables: " << origNumVars << endl;
        cout << "c   - Auxiliary variables: " << monos_vec.size() << endl;
        cout << "c   - Total variables: " << solver->nVars() << endl;
        
        if (verbosity >= 2) {
            cout << "c Product terms (monomials) found: " << monos_vec.size() << endl;
            if (monos_vec.size() > 0 && verbosity >= 3) {
                cout << "c Auxiliary variable mapping:" << endl;
                uint32_t aux_start = solver->nVars() - monos_vec.size();
                for (size_t i = 0; i < monos_vec.size(); i++) {
                    const auto &mono = monos_vec[i];
                    cout << "c   y_" << (aux_start + i + 1) << " = ";
                    for (size_t j = 0; j < mono.size(); j++) {
                        if (j > 0) cout << " & ";
                        cout << "x_" << mono[j].var() + 1;
                        if (mono[j].sign()) cout << "'";
                    }
                    cout << endl;
                }
            }
        }
        cout << "c ==========================================" << endl;
    }

    return true;
}

} // namespace CMSat
