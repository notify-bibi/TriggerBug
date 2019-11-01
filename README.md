# TriggerBug
Under construction.....

The C++ Dynamic symbolic executor like angr.

The engine was developed to solve some of angr's more intractable problems.

	进展：
	python前端准备重写，结构太复杂。
	很幸运解决了并提供求解DES等一些列现代加密算法的方案。（原理层方案，非自己实现deDes）。demo example有，某些隐式加密在原理上是解不开的，只能爆破，故准备写一个常见现代加密算法的crypto ANAlyzer, 方便构建exp，不需要hook table_base进行显式转换。
	符号地址读写策略变更，之前是求解子集再读写，速度极慢，现在实现了超集求解算法，快速极快一毫秒不到。再根据求得的超集读写。
	实现了xsave指令的微操作，修复xrstor指令（延迟绑定函数存在该两条指令）
	努力构想 自动合并路径的算法。。。。。。（难肝） (目前只能全手动exp写合并)
	计划写反ollvm控制流平坦化的算法。
	
	tips:  不浪费你的时间
	examples的exp很旧了，前端也没更新用不了，也不推荐查看，接口还在更新。 
	对于使用者 目前不建议您深入了解该工具，变更较大。

ing.....。

### Advantages：The present does not represent the future

|        | Angr  | TriggerBug |
| ------ | ------ | ------ |
|the code|-----------------\|   \|-------------------|------------------------------------------|
| model  | -unicorn(fast)--\|  \|--angr engine-| 【real&symbol】Completely mixed|
|language| -----c/c++ ----\|  \| -python(slowly)-| c++/c(Fast) |
|translator| -----qemu ----\|  \| -valgrind(Single)-|  valgrind(Multi) |
|solve thread|Single thread|Multi-threaded|
|compress state method|semi-automatic|manual|
|guest arch|Common arch|AMD64/X86|
|binary load|python module:cle(Incomplete loading)slowly|(python)memdump from ida(1:1 Fully symbolic loading)fast|
|speed| |like qemu|

..
It is possible that I have misunderstood angr, so I apologize again

## Make
Now only support win64 host machine. Use camke and Visual Studio 2019 with Intel compiler.


# Release
[Dlls & python module][Plre]
## How to use   

```cmd
cd ./TriggerBug/PythonFrontEnd
python setup.py install
```

Put the ```TriggerBug\PythonFrontEnd\ida-plugins``` folder in ```${ your installation path of ida }```

open ida, make a backpoint(bpt). When you get to the bpt, you need to delete the bpt and ```(Shift-2)``` to dump binary.

Then add ```path of [xxx.dump] file``` at 

[Simulator configuration file: TriggerBug-default32][Plxml]

Finally， Modify some simulator configurations in ```[TriggerBug-default32.xml]```.

```python
import TriggerBug
# import z3 # Don't use the built-in z3 module
import TriggerBug.z3 as z3
top_state = TriggerBug.TopState(file_name=r'./Roads.xml',need_record=True)
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
test ok
```

### [examples][Pltest]

# Salute to you
Thanks to the developers of the  [Z3][Plz3] ,[Valgrind][Plvgrd] and [Angr][Plangr] projects.

I patched the Valgrind to support multi-thread.
# Development
Want to contribute? Great!

Warmly welcome to join us in the development. Study together.


   [Plvgrd]: <http://valgrind.org/>
   [Plz3]: <https://github.com/Z3Prover/z3>
   [Plangr]: <https://github.com/angr>
   [Pltest]: <https://github.com/notify-bibi/TriggerBug/tree/master/PythonFrontEnd/examples>
   [Plre]: <https://github.com/notify-bibi/TriggerBug/releases>
   [Plxml]: <https://github.com/notify-bibi/TriggerBug/blob/master/PythonFrontEnd/TriggerBug-default32.xml>
