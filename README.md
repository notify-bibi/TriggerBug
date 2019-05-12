# TriggerBug
Under construction.....

The C++ Dynamic symbolic executor like angr.

The engine was developed to solve some of angr's more intractable problems.

examples的exp还没写。
目前还不建议深入了解该工具，接口还没写完整

### Advantages：The present does not represent the future

|        | Angr  | TriggerBug |
| ------ | ------ | ------ |
|the code|-----------------\|   \|-------------------|------------------------------------------|
| model  | -unicorn(fast)--\|  \|--angr engine-| 【real&symbol】Completely mixed|
|language| -----c/c++ ----\|  \| -python(slowly)-| c++/c(Fast) |
|translator| -----qemu ----\|  \| -valgrind(Single)-|  valgrind(Multi) |
|solve thread|Single thread|Multi-threaded|
|thread of emu process|Single thread|Multi-threaded|
|compress state method|semi-automatic|manual|
|guest arch|Common arch|only AMD64(Subsequent support for other architectures)|
|host arch/system|Common arch/system|AMD64/win64(Subsequent support for other architectures)|
|binary load|python module:cle(Incomplete loading)slowly|(python)memdump from ida(1:1 Fully symbolic loading)fast|
|speed| |like qemu|

..
It is possible that I have misunderstood angr, so I apologize again

## Make
Now only support win64 host machine. Use camke and Virual Studio 2017 with Intel compiler.

# Release
[Dlls & python module][Plre]
## How to use   
Put the ```TriggerBug.dll and libz3.dll  you download ``` in ```TriggerBug\PythonFrontEnd\TriggerBug\libs```
```cmd
cd ./TriggerBug/PythonFrontEnd
python setup.py install
```

Put the ```TriggerBug\PythonFrontEnd\ida-plugins``` folder in ```${ your installation path of ida }```

open ida, make a backpoint(bpt). When you get to the bpt, you need to delete the bpt and ```(Shift-2)``` to dump binary.

Then add ```path of [xxx.dump] file``` at 

[binaryVexConfig.xml][Plxml]

Finally， Modify some simulator configurations in ```[binaryVexConfig.xml]```.

```python
import TriggerBug
# import z3 # Don't use the built-in z3 module
import TriggerBug.z3 as z3
top_state = TriggerBug.TopState(file_name=r'./easygo.xml',need_record=True)
name:           .rodata address:0000000000496000 data offset:00000008ce length:000004e99a
name:        .noptrdata address:000000000055f000 data offset:000004f270 length:000000ccfc
name:            [vdso] address:00007ffff7ffe000 data offset:000005bf9c length:0000001000
name:             .text address:0000000000401000 data offset:000005cfb4 length:00000945a6
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
   [Plxml]: <https://github.com/notify-bibi/TriggerBug/blob/master/PythonFrontEnd/examples/binaryVexConfig.xml>
