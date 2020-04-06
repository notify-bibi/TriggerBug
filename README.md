## TriggerBug

------

本项目编写一年有余，目的就是解决现代符号执行的各种困难（路径爆炸，符号地址读写，求解费时，客户机适配工作量大），本项目力求写好约束就可快速得到flag

<center> 目前还未将其向各大平台推广（改动大，python前端同步困难），计划最迟到今年年底再推送。</center>

tips:  You can save time. It is not recommended that you understand the tool at present, the front end is not updated. But you can experiment with the c++ back end as a developer. Under construction.....

The C++ Dynamic symbolic executor like Angr.
The engine was developed to solve some of Angr's more intractable problems.

	进展：
	1. python前端准备重写，结构太复杂。
	2. 解决了并提供求解AES等一些列现代加密算法的方案。（原理层方案，非自己实现Aes decrypto。demo example有实例）。某些隐式加密在原理上是解不开的，只能爆破，故准备写一个常见现代加密算法的crypto ANAlyzer, 方便构建exp，不需要hook table_base进行显式转换。
	3. 符号地址读写策略变更，之前是求解子集再读写，速度极慢，现在实现了超集求解算法，快速极快。再根据求得的超集读写。
	4. 自动合并路径的算法已经构造完毕.
	5. 代码控制流块探索算法完成，计划写主动式路径合并分析器，正在完善。。。。。。 (目前只有被动式的可以自动合并分支，某些子状态回收不是很好)
	6. 计划写反ollvm控制流平坦化的算法。
	7. crypto_finder算法完成，现代加密算法的隐式关系表还太少
	8. 采用模拟host code实现guest code的方法去支持所有ir dirty code（guest code 的微操作）和ir dirty call, 但switch结构微操作尚未支持（使用if结构替换可解决【效率低】，或者直接实现微操作到z3_target_call项目代码中替换dirty call【效率高】）。[原因：本方法是将客户机寄存器和内存映射到模拟宿主机，客户机模拟微指令只可以使用宿主机的栈，switch结构的静态表不属于模拟栈。


​	ing.....

### Advantages：The present does not represent the future

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

It is possible that I have misunderstood angr, so I apologize again

## Make
------

​        Now only support win64 host machine. Use camke and Visual Studio 2019 with Intel compiler.


## Release
------

​        [Dlls & python module][Plre]

## Install 

------
```cmd
cd ./TriggerBug/PythonFrontEnd
python setup.py install
```

​       Put the [TriggerBug\PythonFrontEnd\ida-plugins][MDB] folder in ```${ your installation path of ida }```

## Usage
------

open ida, make a backpoint(bpt). When you get to the bpt, you need to delete the bpt and ```(Shift-2)``` to dump binary.

```
介绍下c++写代码使用引擎技巧（需要构建）
python前端用不了，敬请期待
例如 examples 的ctf题目 xctf-asong
建议先试着您的使用ctf技巧逆向该题目，再看下面的代码。
此题使用angr必定路径爆炸，某些模拟执行的地址访问可能是符号地址访问，angr可能会直接将该state添加到Death的state管理器

下面使用本引擎
速度很快的，主要是z3太耗时，如果没有大量处理符号，仿真速度基本不用担心


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

不到30s解出

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
还有个vmp题目，可以借助本工具看到它的实际加密逻辑（污点追踪）
```

###     [examples][Pltest] 

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