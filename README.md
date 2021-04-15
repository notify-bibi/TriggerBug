<center> TriggerBug</center>

------

**tips:**  

You can save time. It is not recommended that you understand the tool at present, the front end is not updated. But you can experiment with the c++ back end as a developer. Under construction.....

The C++ Dynamic symbolic executor like Angr.
The engine was developed to solve some of Angr's more intractable problems.

进展：

- [x] 解决了并提供求解AES等一些列现代加密算法的方案。（原理层方案，非实现Aes decrypto。demo example有实例）。某些隐式加密在原理上是解不开的，只能爆破，故准备写一个常见现代加密算法的crypto ANAlyzer, 方便构建exp，不需要hook table_base进行显式转换。crypto_finder(目前仅添加支持aes)
- [x] 采用模拟host code实现guest code的方法去支持所有ir dirty code（guest code 的微操作）和ir dirty call, dirty call regs合并到客户机regs末尾，并挂载到guest memory map 上，以此实现dirty call支持完整性， 将host dirty call分解为target_ir_call和标准ir指令来支持执行。host dirty call stack使用客户机未分配区，IRDirty class 管理生命周期，设计原理限制，无法递归。
- [x] 符号地址读写策略变更，之前是求解子集再读写，速度极慢，现在实现了超集求解算法，快速极快。再根据求得的超集读写。
- [x] 自动合并路径的算法已经构造完毕. 路径爆炸缓解方案详见文末
- [x] 移植，计划将代码部署在linux、darwin、windows(clang)
- [x] 反反调试功能（vmp检测通过）
- [x] 代码重构，所有基础符号变量全部使用basic_var.hpp中的sv::模版类，涵盖所有操作，编译时期确定并计算参数（提速），编译时检查所有AST误操作等问题。
- [x] windows ntdll_KiUserExceptionDispatcher 异常支持（Eha/ EHsc）vmp喜欢异常检测.
- [x] 支持模拟windows wow64嵌套子系统，支持cpu长模式和32位模式动态切换， 需要配合windbg, 内核全部使用64位
- [ ] Python前端重写（结构太复杂、项目重构不易同步）推迟。
- [x] 代码控制流目标路径探索算法完成，计划写主动式路径合并分析器，正在完善 (目前只有被动式的可以自动合并分支，某些子状态回收不是很好) 
- [ ] 设计分析器，使用valgrind优化block，日志型模拟基本块，记录执行指令分析，分析循环条件等手段来解决问题。在原理上，对于很多大型程序，符号执行并不能构建出程序的所有的执行状态，时间复杂度O(k^n)，加入各种预测约束、快速解析符号地址遍历读写技术、状态合并技术、Cr3用户页复制等也仅仅是一种缓解手段，但不是说没有用，其在无环路分支上表现非常好。挖坑 ...
- [ ] VMP等强壳的随机地址解密释放代码再执行会干扰分析器，地址不再具有意义，irsb和hash进行绑定，有待解决
- [x] 添加IRU cache模块，加快翻译速度，已完成
- [ ] 设计将分析指令流的寄存器读写，对未读后写的寄存器操作进行分析剔除，用于反指令混淆，但是表现不佳，考虑将IR tree经过准换为z3 ast,使用z3优化器反混淆，但是需要z3 ast 2 ir tree, 构建ing
- [ ] 设计basic block分析模块，将不再操作任何客户机寄存器，使用中间变量ir进行表达内存操作与交换.基本块树构建完整性由符号执行探索，未命中返回使用后端继续探索。可以以此设计IR层的反编译调试器，设计中

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
|speed| Orz  🙏 |like qemu|



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
$ cmake -G "Visual Studio 16 2019" -T ClangCL X:\TriggerBug
  pls use MSBuild IDE
```

**interesting dev option**

`-DDEBUG_GABLE=ON`
`-DZ3_BUILD_LIBZ3_SHARED=ON `
`-DZ3_USE_LIB_GMP=OFF `
`-DZ3_SINGLE_THREADED=OFF `

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



Now you need to open Windbg server

```powershell

bcdedit.exe -set debug on
bcdedit.exe -dbgsettings net hostip:127.0.0.1 port:50000
bcdedit -dbgsettings
```

Open ida, **switch windbg** ->**connect string  tcp:server=127.0.0.1,port=50000** -> **make a backpoint(bpt)**. 

When you hit one bpt.  At the Windbg commond line , **enter !sw**   to open wow64exts. (不然32位程序一个含有系统调用的库函数都不可执行)

Just **(Shift-3)** to dump binary.

```powershell
WINDBG>!sw
Switched to Host mode
.sel :20  .base :0x0  .limit :ffffffff  .flags :cfb
.sel :28  .base :0x0  .limit :ffffffff  .flags :cf3
.sel :50  .base :0x241000  .limit :fff  .flags :4f3
+ ------------- +----------------------+--------------------+----------+--------+
| ----segment-- |          VA          |        size        |   flag   | status |
+ ------------- +----------------------+--------------------+----------+--------+
| debug001      |               10000  |    10000 ->    64kb|    12    |   ok   |
| Project1.exe  |              400000  |     1000 ->     4kb|    12    |   ok   |
| Project1.exe1 |              401000  |    10000 ->    64kb|    12    |   ok   |
| Project1.exe2 |              411000  |     c000 ->    48kb|     8    |   ok   |
| Project1.exe3 |              41d000  |     3000 ->    12kb|    12    |   ok   |
| Project1.exe4 |              420000  |     1000 ->     4kb|    12    |   ok   |
....
| wow64cpu      |            770b0000  |     1000 ->     4kb|    12    |   ok   |
| wow64cpu6     |            770b7000  |     2000 ->     8kb|    12    |   ok   |
| ntdll         |            770c0000  |     1000 ->     4kb|    12    |   ok   |
| ntdll1        |            770c1000  |   11d000 ->  1140kb|    12    |   ok   |
| ntdll3        |            771e4000  |    78000 ->   480kb|    12    |   ok   |
| debug038      |            7fe40000  |     5000 ->    20kb|    12    |   ok   |
| wow64win5     |        7ffdd28fd000  |     f000 ->    60kb|    12    |   ok   |
| ntdll4        |        7ffdd2c50000  |     1000 ->     4kb|    12    |   ok   |
+ ------------- +----------------------+--------------------+----------+--------+
 (rax        IR_offset: 16   ) (val:                           19ffcc nb:  8)
 ....
 (rbp        IR_offset: 56   ) (val:                           19ff80 nb:  8) 
 (r8         IR_offset: 80   ) (val:                         77133c90 nb:  8)
 (r15        IR_offset: 136  ) (val:                         770b3600 nb:  8) 
 (st0        IR_offset: 776  ) (val:                                0 nb:  8) 
 (st7        IR_offset: 832  ) (val:                                0 nb:  8) 
 (cs         IR_offset: 936  ) (val:                               23 nb:  2) 
 (ss         IR_offset: 946  ) (val:                               2b nb:  2) 
 (fs         IR_offset: 942  ) (val:                               53 nb:  2) 
 (gs         IR_offset: 944  ) (val:                               2b nb:  2) 
 (ymm0       IR_offset: 224  ) (val:                                0 nb: 32) 
 (ymm15      IR_offset: 704  ) (val:                                0 nb: 32) 
 (cc_op      IR_offset: 144  ) (val:                                0 nb:  8) 
 (cc_dep1    IR_offset: 152  ) (val:                              246 nb:  8) 
 (cc_dep2    IR_offset: 160  ) (val:                                0 nb:  8) 
 (cc_ndep    IR_offset: 168  ) (val:                                0 nb:  8) 
 (idflag     IR_offset: 200  ) (val:                                0 nb:  8) 
 (acflag     IR_offset: 192  ) (val:                                0 nb:  8) 
 (fptag      IR_offset: 840  ) (val:                                0 nb:  8) 
 (ftop       IR_offset: 768  ) (val:                                8 nb:  4) 
 (fpround    IR_offset: 848  ) (val:                                0 nb:  8) 
 (sseround   IR_offset: 216  ) (val:                                0 nb:  8) 
 (gdt        IR_offset: 928  ) (val:                     8000fff00000 nb:  8) 
 (dflag      IR_offset: 176  ) (val:                                1 nb:  8) 
 (gs_const   IR_offset: 904  ) (val:                           23f000 nb:  8) 
 (fs_const   IR_offset: 208  ) (val:                                0 nb:  8) 
dump success:  Y:\vmp\Project1.vmp.exe.dump
term() called!
```



介绍下c++写代码使用引擎技巧

例如 examples 的ctf题目 xctf-asong.  本引擎不到20s解出, angr用时4分钟

此题使用angr必定路径爆炸，某些模拟执行的地址访问可能是符号地址访问，angr可能会直接将该state添加到Death的state管理器

库函数底层调用系统调用可能才会失败，比如malloc、printf、微软闭源库函数等均无问题（sys_brk、nt_proc_information、非标准IO等系统调用已经实现）

下面使用本引擎，速度很快, 不用担心某符号执行引擎跑进VMP出不来了 ：）

主要是z3太耗时，如果没有大量处理符号，仿真速度基本不用担心



[shift-3] dump it

![image-20210224233526227](https://github.com/notify-bibi/TriggerBug/blob/master/doc/readme/example_dump.png)

```

```


```c++
TriggerBug\src\test\test_main.cxx

State_Tag success_ret3(StateBase& s) {
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s.regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    VexGuestAMD64State& amd64_reg_state = s.get_regs_maps()->guest.amd64;
    for (int i = 0; i < 38; i++) {
        auto e = s.mem.load<Ity_I8>(enc + i);
        s.solv.add(e == (UChar)bf[i]);
    }
    printf("checking\n\n");
    auto ret = s.solv.check();
    if (ret == z3::sat) {
        printf("issat");
        auto m = s.solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        printf("unsat???\n\n%d", dfdfs);
    }
    s.solv.pop();
    return Death;
}


int main() {
    vex_context v(1);
    v.param().set("ntdll_KiUserExceptionDispatcher", (void*)0x777B3BC0);
    v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
    TR::State state(v, VexArchX86);
    state.read_bin_dump("Y:\\vmp\\Project1.vmp.exe.dump");
    

    state.get_trace()->setFlag(CF_traceInvoke);
    //v.hook_read(read);
    v.hook_read(symbolic_read);
    //state.setFlag(CF_ppStmts);
    VexGuestAMD64State& amd64_reg_state = state.get_regs_maps()->guest.amd64;
    state.avoid_anti_debugging();
    auto bts = state.start();
  
    state.hook_add(0x400CC0, success_ret);
    //被动式的 路径爆炸解决方案
    StateAnalyzer gv(state);
    gv.Run();
}


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



goto   [TRtest][trTest]  ;   

goto   [examples program][Pltest]  ;

## Development

------

Want to contribute? Great! 

Set up the development environment ：See  <<[development manual][Develop]>>

**Of course, you can also use this engine to develop your own tools**

Warmly welcome to join us in the development. Study together.



​                               缓解路径爆炸的原理展示

 cmpr::Compress<target_state, ...>, 配合StateAnalyzer（已剔除）

```powershell
                         P1 top
    
            A  (P1 fork)                B  (P1 fork) 
            P2
    
      a1  a2  -a1 -a2              b-1  b0   b1
      Q1  Q2   q1  q2
    
  yes  P2 → (Q1 ∨ Q2) <=> ┐P2 ∨ (Q1 ∨ Q2) <=> ┐P2 ∨ Q1 ∨ Q2
  sat:  P2 Q1 Q2
        1  1  1
        1  0  1
        1  1  0
        0  x  x
  
  yes  P2 → (┐q1 ∧ ┐q2) <=> P2 → ┐(q1 ∨ q2) <=> ┐P2 ∨ (┐q1 ∧ ┐q2) <=> ┐P2 ∨ (┐q1 ∧ ┐q2)
  sat:  P2 q1 q2
        1  0  0
        0  x  x
  a assert
  P1 A B state
  Q sbool rea == sea
  如果分支条件约束未添加，if.else被命中那么很可能会导致求解结果错误。并不是合并就完美解决路径爆炸，如果多个不等返回地址被合并，合并只能增加负荷
```







## Release

------

  ​        [Dlls & python module][Plre]   *need build by yourself*

## Salute to you

------
Thanks to the developers of the  [Z3][Plz3] , [Valgrind][Plvgrd], [Spdloger][Spdlog] and [Angr][Plangr] projects.




[Plvgrd]: <http://valgrind.org/>
[Plz3]: <https://github.com/Z3Prover/z3>
[Plangr]: <https://github.com/angr>
[Pltest]: <https://github.com/notify-bibi/TriggerBug/tree/master/PythonFrontEnd/examples>
[Plre]: <https://github.com/notify-bibi/TriggerBug/releases>
[Develop]: <https://github.com/notify-bibi/TriggerBug/blob/master/develop.md>

[MDB]: <https://github.com/notify-bibi/TriggerBug/blob/master/PythonFrontEnd/ida-plugins/tr_dumper.py>
[CLE]: <https://github.com/angr/cle>

[Spdlog]: <https://github.com/gabime/spdlog>

[trTest]: <https://github.com/notify-bibi/TriggerBug/blob/master/src/test/test_main.cxx>

另外值得高兴的是, vs终终终于支持clang了，早点放弃自家编译器该多好啊，有些时候还是不要那么执着的好 :)

cmake里已经做了ms编译兼容