
#define IR_TEST(func) if (func()) std::cout << "++++++++++++"""#func""" success ++++++++++++" << std::endl; else std::cerr << "-----------"""#func""" faild -----------" << std::endl;

#define TESTCASEDIR "C:\\Users\\notify"
//#define TESTCASEDIR "Z:"

#include "instopt/engine/tr_kernel.h"
#include "instopt/helper/z3_target_call.h"

