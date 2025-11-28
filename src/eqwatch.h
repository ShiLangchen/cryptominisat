#pragma once

#include <cstdint>
#include <Vec.h>

namespace CMSat
{
class EqWatched
{
  private:
  public:
    EqWatched(int32_t id) : eid(id) {}
    int32_t eid;
};

inline void swap(vec<EqWatched> &a, vec<EqWatched> &b)
{
    a.swap(b);
}
} // namespace CMSat