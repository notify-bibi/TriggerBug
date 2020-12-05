<center> TriggerBug</center>

------

**tips:**  

You can save time. It is not recommended that you understand the tool at present, the front end is not updated. But you can experiment with the c++ back end as a developer. Under construction.....

The C++ Dynamic symbolic executor like Angr.
The engine was developed to solve some of Angr's more intractable problems.

进展：

- [x] 解决了并提供求解AES等一些列现代加密算法的方案。（原理层方案，非实现Aes decrypto。demo example有实例）。某些隐式加密在原理上是解不开的，只能爆破，故准备写一个常见现代加密算法的crypto ANAlyzer, 方便构建exp，不需要hook table_base进行显式转换。crypto_finder

- [x] 采用模拟host code实现guest code的方法去支持所有ir dirty code（guest code 的微操作）和ir dirty call, 但switch结构微操作尚未支持（使用if结构替换可解决【效率低】，或者直接实现微操作到z3_target_call项目代码中替换dirty call【效率高】）。[原因：本方法是将客户机寄存器和内存映射到模拟宿主机，客户机模拟微指令只可以使用宿主机的栈，switch结构的静态表不属于模拟栈。  

- [x] 符号地址读写策略变更，之前是求解子集再读写，速度极慢，现在实现了超集求解算法，快速极快。再根据求得的超集读写。

- [x] 自动合并路径的算法已经构造完毕.

- [x] 缓解路径爆炸状态合并模块 cmpr::Compress<target_state, ...>

- [x] 

- [x] 移植，计划将代码部署在linux、darwin、windows(clang)

- [x] 反反调试功能（vmp检测通过）

- [x] 代码重构，所有基础符号变量全部使用basic_var.hpp中的sv::模版类，涵盖所有操作，编译时期确定并计算参数（提速），编译时检查所有AST误操作等问题。

- [x] windows 异常支持（Eha/ EHsc）

- [x] 

- [ ] Python前端重写（结构太复杂、项目重构不易同步）推迟。

- [x] 代码控制流目标路径探索算法完成，计划写主动式路径合并分析器，正在完善。。。。。。 (目前只有被动式的可以自动合并分支，某些子状态回收不是很好) 

  

- [ ] 设计分析器，使用valgrind优化block，日志型模拟基本块，记录执行指令分析，分析循环条件等手段来解决问题。在原理上，对于很多大型程序，符号执行并不能构建出程序的所有的执行状态，时间复杂度O(k^n)，加入各种预测约束、快速解析符号地址遍历读写技术、状态合并技术、Cr3用户页复制等也仅仅是一种缓解手段，但不是说没有用，其在无环路分支上表现非常好。挖坑 ...

- [ ] VMP等强壳的随机地址解密释放代码再执行会干扰分析器，地址不再具有意义，irsb和hash进行绑定，有待解决

坚持✊

## advantage

|         |  Angr  | TriggerBug |
| :---------:  | ------ | ------ |
| the code |-----------------\|   \|-------------------|------------------------------------------|
| model   | -unicorn(fast)--\|  \|--angr engine-| 【real&symbol】Completely mixed|
|language | -----c/c++ ----\|  \| -python(slowly)-| c++/c(Fast) |
|translator| ----- qemu ----\|  \| -valgrind(Single)-|  valgrind(Multi) |
|solve thread|Single thread|Multi-threaded|
|compress State|support(Is not very good)|support(automatically)|
|vex(dirtycall)|Incomplete support<br />Implementation by developers|fully supported<br />emu all host code|
|binary load|[py module:cle(Incomplete loading)<br />Parsing is not complete<br />slowly][CLE]|[py dump mem from  IDA <br/>1:1 Fully symbolic loading<br/>200MB/1s][MDB]|
|speed| ... |like qemu|



## shortcomings：

|  all Arch  | X86,AMD64,ARM,ARM64,PPC32,PPC64,S390X,MIPS32,MIPS64 |
| :--: | ---- |
| MEM dump support | X86,AMD64（Under construction..） [CLE][CLE] can give you more supports |

``It is possible that I have misunderstood angr, so I apologize ``

## Make

**darwin**、**linux**

```bash
$ mkdir build && cmake .. && make
```

**-G Xcode** with Xcode

In  **windows**

```bash
cmake -G "Visual Studio 16 2019" -T ClangCL X:\TriggerBug
pls use ms build IDE
```

**dev option**

`-DDEBUG_GABLE=ON`
`-DZ3_BUILD_LIBZ3_SHARED=ON `
`-DZ3_USE_LIB_GMP=OFF `
`-DZ3_SINGLE_THREADED=OFF `



## Release

------

​        [Dlls & python module][Plre]

## Install 

------
前端暂不可用

```cmd
cd ./TriggerBug/PythonFrontEnd
python setup.py install
```

​       Put the [TriggerBug\PythonFrontEnd\ida-plugins][MDB] folder in ```${ your installation path of ida }```

## Usage
------

open ida, make a backpoint(bpt). When you get to the bpt. Just **(Shift-2)** to dump binary.

介绍下c++写代码使用引擎技巧
例如 examples 的ctf题目 xctf-asong
此题使用angr必定路径爆炸，某些模拟执行的地址访问可能是符号地址访问，angr可能会直接将该state添加到Death的state管理器
库函数底层调用系统调用可能才会失败，比如malloc、printf、微软闭源库函数等均无问题（sys_brk、nt_proc_information、非标准IO等系统调用已经实现）

下面使用本引擎
速度很快的，主要是z3太耗时，如果没有大量处理符号，仿真速度基本不用担心

```

[shift-2] dump it
+-------------------+----------------------+--------------------+----------+--------+
|      segment      |          VA          |        size        |   flag   | status |
+-------------------+----------------------+--------------------+----------+--------+
| LOAD              |              400000  |      f9c ->     3kb|    16    |   ok   |
| .text             |              401000  |    a0ae5 ->   642kb|    16    |   ok   |
| Roads             |              4a1ae5  |      51b ->     1kb|    12    |   ok   |
...........
| [heap]            |              5a16d8  |      928 ->     2kb|    12    |   ok   |
| [vvar]            |        7ffff7ffa000  |     3000 ->    12kb|    12    |   war  |
+-------------------+----------------------+--------------------+----------+--------+
| [vvar]            |        7ffff7ffa000  |      400 ->     1kb|    12    |  faild |
+-------------------+----------------------+--------------------+----------+--------+
| [vdso]            |        7ffff7ffd000  |     2000 ->     8kb|    12    |   ok   |
| [stack]           |        7ffffffde000  |    21000 ->   132kb|    12    |   ok   |
| [vsyscall]        |    ffffffffff600000  |     1000 ->     4kb|    12    |   ok   |
+-------------------+----------------------+--------------------+----------+--------+
........
```


```c++
编辑TriggerBug\src\test\test_main.cxx

State_Tag success_ret(State<Addr64>& s) {
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s.regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    for (int i = 0; i < 38; i++) {
        auto e = s.mem.load<Ity_I8>(enc + i);
        s.solv.add(e == (UChar)bf[i]);
    }
    vex_printf("checking\n\n");
    if (s.solv.check() == z3::sat) {
        vex_printf("issat");
        auto m = s.solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        vex_printf("unsat?\n\n");
    }
    s.solv.pop();
    return Death;
}

int main() {
    vex_context<Addr64> v(VexArchAMD64, 4/*threads*/, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.dump");
    SP::linux64 state(v, 0, True);
    state.setFlag(CF_ppStmts);
    state.setFlag(CF_traceJmp);
    for (int i = 0; i < 38; i++) {
        auto flag = state.mk_int_const(8).tos<false, 8>();
        auto g = flag >= 1u && flag <= 128u;
        state.mem.store(state.regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI) + i, flag);
        state.solv.add_assert(g);
    }
    state.hook_add(0x400CC0, success_ret);
    //被动式的 路径爆炸解决方案
    StateAnalyzer gv(state);
    gv.Run();
}

不到20s解出, angr用时4分钟

PS: TriggerBug\PythonFrontEnd\examples> python .\str2flag.py "sat(define-fun p_20 () (_ BitVec 8)
>>   #x66)
>> (define-fun p_24 () (_ BitVec 8)
>>   #x79)
>> (define-fun p_8 () (_ BitVec 8)
>>   #x6c)
>> (define-fun p_23 () (_ BitVec 8)
>>   #x5f)
..................................
>> (define-fun p_32 () (_ BitVec 8)
>>   #x64)
>> (define-fun p_0 () (_ BitVec 8)
>>   #x74)
>> (define-fun p_35 () (_ BitVec 8)
>>   #x61)
>> (define-fun p_4 () (_ BitVec 8)
>>   #x5f)"
namespace: <p_>       len: 38{
        chars     : <that_girl_saying_no_for_your_vindicate>
        chars     : < t h a t _ g i r l _ s a y i n g _ n o _ f o r _ y o u r _ v i n d i c a t e>
        hexstring = "746861745f6769726c5f736179696e675f6e6f5f666f725f796f75725f76696e646963617465"
        p_buff[38] = {0x74,0x68,0x61,0x74,0x5f,0x67,0x69,0x72,0x6c,0x5f,0x73,0x61,0x79,0x69,0x6e,0x67,0x5f,0x6e,0x6f,0x5f,0x66,0x6f,0x72,0x5f,0x79,0x6f,0x75,0x72,0x5f,0x76,0x69,0x6e,0x64,0x69,0x63,0x61,0x74,0x65};

}
[patch_byte(addr+i, ord(v)) for i,v in enumerate(base64.b16decode(hexstring))]（ida python）
    
本引擎提供基本的反反调试功能、支持windows异常、支持解AES(隐式关系)
也可以看看creakme一题，一个aes的题目，上面的特性全部能够展露
```

goto   [examples][Pltest]  ;

## Salute to you

------
Thanks to the developers of the  [Z3][Plz3] ,[Valgrind][Plvgrd] and [Angr][Plangr] projects.



## Development 
------

Want to contribute? Great! 

Set up the development environment ：See  <<[development manual][Develop]>>

**Of course, you can also use this engine to develop your own tools**


Warmly welcome to join us in the development. Study together.


[Plvgrd]: <http://valgrind.org/>
[Plz3]: <https://github.com/Z3Prover/z3>
[Plangr]: <https://github.com/angr>
[Pltest]: <https://github.com/notify-bibi/TriggerBug/tree/master/PythonFrontEnd/examples>
[Plre]: <https://github.com/notify-bibi/TriggerBug/releases>
[Plxml]: <https://github.com/notify-bibi/TriggerBug/blob/master/PythonFrontEnd/TriggerBug-default32.xml>
[Develop]: <https://github.com/notify-bibi/TriggerBug/blob/master/develop.md>

[MDB]: <https://github.com/notify-bibi/TriggerBug/blob/master/PythonFrontEnd/ida-plugins/memory_dump_BIN.py>
[CLE]: <https://github.com/angr/cle>



另外值得高兴的是，windows终于支持clang了，早点放弃自家编译器该多好啊，有些时候还是不要那么执着的好