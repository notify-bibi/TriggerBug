import re
import os

original_dir = './original\\'


def file_name(file_dir):
    NAME = []
    for root, dirs, files in os.walk(file_dir):
        for file in files:
            nam = os.path.splitext(file)[1]
            if nam in ['.cpp', '.c', '.h', '.hpp', '.cxx', '.cx', '.c++'] and original_dir not in root:
                NAME.append(os.path.join(root, file))

    return NAME


NAME = file_name("./")

for filename in NAME:

    file = open(filename, 'r', encoding='utf-8')
  
    print(filename.replace(original_dir, ''))
    try:
        o_code = file.readlines()
    except Exception as e:
        print("****************************************8",filename, e)
        continue
    file.close()
    try:
        os.makedirs(os.path.split(filename)[0])
    except:
        pass
    patchedfile = open(filename, 'w+', encoding='utf-8')
    print(filename)
    new_code = ''
    for index, code in enumerate(o_code):
        if ("long" in code) :
            if "long long" in code:
                print("line:",index,code)
            elif "longlong" not in code :
                if code[code.find("long")+4:code.find("long")+5]==' ':
                    print("patched:line:",index,code[:-1],end=" >> ")
                    code=code.replace("long","long long")
                    print(code)
        new_code+=code
    patchedfile.write(new_code)
    patchedfile.close()
