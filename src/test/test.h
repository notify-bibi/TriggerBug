
#define IR_TEST(func) if (func()) std::cout << "++++++++++++"""#func""" success ++++++++++++" << std::endl; else std::cerr << "-----------"""#func""" faild -----------" << std::endl;
#define PROJECT_DIR "C:\\Users\\bibi\\Desktop\\TriggerBug\\"

#include "engine/tr_main.h"
#include "engine/guest_arch_win32.h"
#include "engine/guest_arch_win64.h"
#include "engine/guest_arch_linux32.h"
#include "engine/guest_arch_linux64.h"