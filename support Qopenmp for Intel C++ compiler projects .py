import re
import os
import xml.dom.minidom as xmldom
import xml.etree.ElementTree as ET
from lxml import etree

original_dir = '.\\build\\'


def file_name(file_dir):
    NAME = []
    for root, dirs, files in os.walk(file_dir):
        for file in files:
            nam,low = os.path.splitext(file)
            if low in ['.vcxproj'] and original_dir in root and "INSTALL" != nam and 'CMakeFiles' not in root:
                NAME.append(os.path.join(root, file))

    return NAME

c1 = "<AdditionalOptions>%(AdditionalOptions) /Qopenmp</AdditionalOptions>"
c2 = "<OpenMP>GenerateParallelCode</OpenMP>"
c3 = "<LanguageStandard>stdcpp14</LanguageStandard>"
c4 = "<Optimization>MaxSpeedHighLevel</Optimization>"
c5 = "<BufferSecurityCheck>false</BufferSecurityCheck>"
c6 = "<UseIntelOptimizedHeaders>true</UseIntelOptimizedHeaders>"


print('add options:\n',c1,'\n',c2,'\n',c3,'\n',c4,'\n',c5,'\n',c6, ' \n\n')
for filename in file_name(original_dir):
    DOMTree = xmldom.parse(filename)
    it = DOMTree.getElementsByTagName("ItemDefinitionGroup")
    if it:
        for Item in it:
            ClCompile = Item.getElementsByTagName("ClCompile")
            if not ClCompile:
                break
            a = ClCompile[0]

            if not a.getElementsByTagName("AdditionalOptions"):
                b = DOMTree.createElement("AdditionalOptions")
                b.appendChild(DOMTree.createTextNode('%(AdditionalOptions) /Qopenmp'))
                a.appendChild(b)

            if not a.getElementsByTagName("UseIntelOptimizedHeaders"):
                b = DOMTree.createElement("UseIntelOptimizedHeaders")
                b.appendChild(DOMTree.createTextNode('true'))
                a.appendChild(b)
            
            if not a.getElementsByTagName("OpenMP"):
                c = DOMTree.createElement("OpenMP")
                c.appendChild(DOMTree.createTextNode('GenerateParallelCode'))
                a.appendChild(c)

            if not a.getElementsByTagName("BufferSecurityCheck"):
                c = DOMTree.createElement("BufferSecurityCheck")
                c.appendChild(DOMTree.createTextNode('false'))
                a.appendChild(c)
            else:
                BufferSecurityCheck = a.getElementsByTagName("BufferSecurityCheck")[0]
                a.removeChild(BufferSecurityCheck)
                d = DOMTree.createElement("BufferSecurityCheck")
                d.appendChild(DOMTree.createTextNode('false'))
                a.appendChild(d)

            if ('z3' not in filename.split('\\')) and (len(a.getElementsByTagName("LanguageStandard"))==0):
                d = DOMTree.createElement("LanguageStandard")
                d.appendChild(DOMTree.createTextNode('stdcpp17'))
                a.appendChild(d)

            
            
            if(Item.getAttribute("Condition").split("==")[1]=="'Release|x64'"):
                Optimization = a.getElementsByTagName("Optimization")
                if  len(Optimization):
                    Optimization = Optimization[0]
                    if (Optimization.firstChild.nodeValue != "MaxSpeedHighLevel"):
                        a.removeChild(Optimization)
                        d = DOMTree.createElement("Optimization")
                        d.appendChild(DOMTree.createTextNode('MaxSpeedHighLevel'))
                        a.appendChild(d)
                else:
                    d = DOMTree.createElement("Optimization")
                    d.appendChild(DOMTree.createTextNode('MaxSpeedHighLevel'))
                    a.appendChild(d)

                
                
        try:
            with open(filename, 'w+', encoding='UTF-8') as fh:
                DOMTree.writexml(fh, indent='', addindent='  ', newl='', encoding='UTF-8')
                print(filename, '写入xml OK!')
        except Exception as err:
            print('错误信息：{0}'.format(err))
    else:
        print(filename, '错误信息：无 ItemDefinitionGroup : {0}'.format(it))

