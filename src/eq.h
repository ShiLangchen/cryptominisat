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
    const Lit get_aux_lit() const { return aux_lit; }
    int32_t get_eid() const { return eid; }
    uint32_t watched[2] = {0, 1};

    const Lit &operator[](const uint32_t at) const { return lits[at]; }
    Lit &operator[](const uint32_t at) { return lits[at]; }
    uint32_t size() const { return (uint32_t)lits.size(); }
};
} // namespace CMSat