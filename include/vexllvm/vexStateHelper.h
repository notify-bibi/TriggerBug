#pragma once

extern "C" {
#include <libvex.h>
#include <libvex_ir.h>
}
class StateHelper {
public:
  virtual const char *regOff2name(UInt off) = 0;
};
