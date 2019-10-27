#ifndef _TR_head
#define _TR_head
#define _SILENCE_STDEXT_HASH_DEPRECATION_WARNINGS
#include <hash_map>
#include <windows.h>
#include <mmintrin.h>  //MMX
#include <xmmintrin.h> //SSE(include mmintrin.h)
#include <emmintrin.h> //SSE2(include xmmintrin.h)
#include <pmmintrin.h> //SSE3(include emmintrin.h)
#include <tmmintrin.h> //SSSE3(include pmmintrin.h)
#include <smmintrin.h> //SSE4.1(include tmmintrin.h)
#include <nmmintrin.h> //SSE4.2(include smmintrin.h)
#include <wmmintrin.h> //AES(include nmmintrin.h)
#include <immintrin.h> //AVX(include wmmintrin.h)
#include <intrin.h>    //(include immintrin.h)
#include <iostream>
#include <fstream>
#include <sstream>
#include <tuple>
#include <exception>
#include <string>
#include <vector>
#include <queue>
#include <memory>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <future>
#include <functional>
#include <stdexcept>
#include <iomanip>
#include "c++/z3++.h"


#ifdef DLL_EXPORTS
#define DLLDEMO_API __declspec(dllexport)
#else
#define DLLDEMO_API __declspec(dllimport)
#endif

#undef Py_LIMITED_API
#include <python\Python.h>


#include "Engine/header.hpp"
#include "Engine/functions/functions.hpp"
#include "Engine/Thread_Pool/ThreadPool_CD.hpp"



#endif _TR_head