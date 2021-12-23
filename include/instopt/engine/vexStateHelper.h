#pragma once

extern "C" {
#include <libvex.h>
#include <libvex_ir.h>
}
#include <memory>
class StateHelper {
public:
  virtual const char *regOff2name(UInt off) = 0;
  static std::shared_ptr<StateHelper> get(VexArch);
};
