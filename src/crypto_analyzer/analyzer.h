#pragma once
#ifndef _ANALYZER_
#define _ANALYZER_
#include "engine/state_class.h"




typedef z3::expr(*ana_decl) (const z3::expr&);
typedef ana_decl(*finder)(UInt, uint32_t);




#endif