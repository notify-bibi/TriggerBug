# TriggerBug
Under construction.....

The C++ Dynamic symbolic executor like angr.

The engine was developed to solve some of angr's more intractable problems.

	进展：
	python前端准备重写，结构太复杂。
	很幸运解决了并提供求解DES等一些列现代加密算法的方案。（原理层方案，非自己实现deDes）。demo example有，准备写个常见现代加密算法的crypto ANAlyzer, 方便构建exp。
	努力构想自动合并路径的算法中。。。。。。（难） (目前只能全手动exp写合并)
	计划写反ollvm控制流平坦化的算法。
	
	tips:  
	不浪费你你时间
	examples的exp还没写完全，也不推荐查看，接口还在更新。 
	对于使用者 我不建议目前还深入了解该工具，接口还没写完整。

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
top_state = TriggerBug.TopState(file_name=r'./easygo.xml',need_record=True)
name:       msvcrt.dll1 address:00000000772e1000 data offset:0006a16229 length:00000b1000
name:       msvcrt.dll2 address:0000000077392000 data offset:0006ac7229 length:0000002000
name:       msvcrt.dll3 address:0000000077394000 data offset:0006ac9229 length:0000004000
name:       msvcrt.dll4 address:0000000077398000 data offset:0006acd229 length:0000007000
name:     TIB[00003EE8] address:00000000002db000 data offset:0006ad4229 length:0000008000
name:     wow64cpu.dll2 address:0000000077493000 data offset:0006adc229 length:0000001000
name:     wow64cpu.dll3 address:0000000077494000 data offset:0006add229 length:0000001000
name:     wow64cpu.dll1 address:0000000077491000 data offset:0006ade229 length:0000002000
name:     wow64cpu.dll6 address:0000000077497000 data offset:0006ae0229 length:0000002000
name:     wow64cpu.dll4 address:0000000077495000 data offset:0006ae2229 length:0000001000
name:     wow64cpu.dll5 address:0000000077496000 data offset:0006ae3229 length:0000001000
name:       registers28 address:000000000000001c data offset:0006ae4229 length:0000000004
name:          debug025 address:0000000006cad000 data offset:0006ae422d length:0000002000
name:          debug024 address:0000000006ba8000 data offset:0006ae622d length:0000008000
name:          debug027 address:0000000006ea0000 data offset:0006aee22d length:0000004000
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
