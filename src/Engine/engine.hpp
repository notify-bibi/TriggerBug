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
#include "api/c++/z3++.h"


#ifdef DLL_EXPORTS
#define DLLDEMO_API __declspec(dllexport)
#else
#define DLLDEMO_API __declspec(dllimport)
#endif

#define Py_LIMITED_API
#ifdef _DEBUG
#undef _DEBUG
#include <python\Python.h>
#define _DEBUG 1
#else
#include <python\Python.h>
#endif

//觉得引擎没bug了就取消注释，加快速度
//#define RELEASE_OFFICIALLY

//客户机为的位宽
#define GUEST_IS_64

//所有客户机寄存器的ir层的最大长度。建议>=100
#define REGISTER_LEN 1000

//100条任意客户机指令所需要的最大 IR temp index。建议>=400
#define MAX_IRTEMP 400

//每个虚拟物理页存在ast时，使用hash保存每一个ast;否则使用Z3_ast[0x1000];前者耗费小，速度稍微慢，后者反之
#define USE_HASH_AST_MANAGER

//copy one write 写时复制，速度快，默认不关闭
//#define CLOSECNW

//父页存在ast就拷贝一页；否则就使用父页，写时再复制(后者速度快)
//#define USECNWNOAST

//宿主机的平台架构
#define HOSTARCH VexArchAMD64

#if defined(GUEST_IS_64)
//客户机的地址类型（size_t）
#define ADDR unsigned long long
#else
//客户机的地址类型（size_t）
#define ADDR unsigned int
#endif


#include "Engine/header.hpp"
#include "Engine/functions/functions.hpp"
#include "Engine/Thread_Pool/ThreadPool_CD.hpp"


class TRcontext :public z3::context {
    friend class State;
    //z3_translate并不是线程安全的，target_ctx不同，ctx相同进行多线程并发也会bug。为了写时复制添加一个锁
    std::mutex translate_mutex;
public:
    inline TRcontext() :z3::context() { }
    inline std::mutex& getLock() { return translate_mutex; };
    inline operator std::mutex& () { return translate_mutex; };
};

//注：intel编译器对四个及四个一下的switch case会自动使用if else结构。
#endif _TR_head