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

//��������ûbug�˾�ȡ��ע�ͣ��ӿ��ٶ�
//#define RELEASE_OFFICIALLY

//�ͻ���Ϊ��λ��
#define GUEST_IS_64

//���пͻ����Ĵ�����ir�����󳤶ȡ�����>=100
#define REGISTER_LEN 1000

//100������ͻ���ָ������Ҫ����� IR temp index������>=400
#define MAX_IRTEMP 400

//ÿ����������ҳ����astʱ��ʹ��hash����ÿһ��ast;����ʹ��Z3_ast[0x1000];ǰ�ߺķ�С���ٶ���΢�������߷�֮
#define USE_HASH_AST_MANAGER

//copy one write дʱ���ƣ��ٶȿ죬Ĭ�ϲ��ر�
//#define CLOSECNW

//��ҳ����ast�Ϳ���һҳ�������ʹ�ø�ҳ��дʱ�ٸ���(�����ٶȿ�)
//#define USECNWNOAST

//��������ƽ̨�ܹ�
#define HOSTARCH VexArchAMD64

#if defined(GUEST_IS_64)
//�ͻ����ĵ�ַ���ͣ�size_t��
#define ADDR unsigned long long
#else
//�ͻ����ĵ�ַ���ͣ�size_t��
#define ADDR unsigned int
#endif


#include "Engine/header.hpp"
#include "Engine/functions/functions.hpp"
#include "Engine/Thread_Pool/ThreadPool_CD.hpp"


class TRcontext :public z3::context {
    friend class State;
    //z3_translate�������̰߳�ȫ�ģ�target_ctx��ͬ��ctx��ͬ���ж��̲߳���Ҳ��bug��Ϊ��дʱ�������һ����
    std::mutex translate_mutex;
public:
    inline TRcontext() :z3::context() { }
    inline std::mutex& getLock() { return translate_mutex; };
    inline operator std::mutex& () { return translate_mutex; };
};

//ע��intel���������ĸ����ĸ�һ�µ�switch case���Զ�ʹ��if else�ṹ��
#endif _TR_head