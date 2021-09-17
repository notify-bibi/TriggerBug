
#define IR_TEST(func) if (func()) std::cout << "++++++++++++"""#func""" success ++++++++++++" << std::endl; else std::cerr << "-----------"""#func""" faild -----------" << std::endl;
#define PROJECT_DIR "Y:\\TriggerBug\\"

#include "instopt/engine/tr_kernel.h"
#include "instopt/engine/z3_target_call/z3_target_call.h"

