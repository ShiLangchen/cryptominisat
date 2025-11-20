#pragma once

#include <vector>
#include "solvertypesmini.h"

namespace CMSat
{
class Eq
{
  private:
    std::vector<Lit> lits;
    Lit aux_lit;
    int32_t eid;

  public:
    Eq(const std::vector<Lit> &_lits, const Lit _aux_lit, const int32_t _eid)
        : lits(_lits), aux_lit(_aux_lit), eid(_eid)
    {
    }
    const std::vector<Lit> &get_lits() const { return lits; }
    const Lit &get_aux_lit() const { return aux_lit; }
    int32_t get_eid() const { return eid; }
};
} // namespace CMSat