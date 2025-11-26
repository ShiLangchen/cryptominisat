#pragma once

#include <cstdint>
namespace CMSat
{
class EqWatched
{
  private:
  public:
    EqWatched(int32_t id) : eid(id) {}
    int32_t eid;
};
} // namespace CMSat