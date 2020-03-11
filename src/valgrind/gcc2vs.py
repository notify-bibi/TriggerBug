import re
import os

original_dir = '.\\original\\'


def file_name(file_dir):
    NAME = []
    for root, dirs, files in os.walk(file_dir):
        for file in files:
            nam = os.path.splitext(file)[1]
            if nam in ['.cpp', '.c', '.h', '.hpp', '.cxx', '.cx', '.c++'] and original_dir in root:
                NAME.append(os.path.join(root, file))

    return NAME


NAME = file_name(original_dir)
mode_c=True
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
        os.makedirs(os.path.split(filename.replace(original_dir, ''))[0])
    except:
        pass
    patchedfile = open(filename.replace(original_dir, '')+('pp' if not mode_c else ""), 'w+', encoding='utf-8')
    new_code = ''
    k = 0
    for index, code in enumerate(o_code):
        if ("include" in code) and not mode_c:
            regex = re.match(
                r'#include[\t| ]*\"'
                r'(?P<head>[A-Za-z0-9_\.]+)'
                r'\"(?P<end>\w+)*[\t| ]*',
                code
            )
            if (regex):
                data = regex.groupdict()
                for _filename in NAME:
                    if os.path.split(_filename)[1] in data["head"]:
                        print(code,end='  >>  ')
                        code=code.replace(data["head"],data["head"]+'pp')
                        print(code)
                        break
        elif "case" in code and "..." in code:
            huakuohao=''
            if '{' in code:
                huakuohao='{'
                
            regex = re.match(
                r'(?P<tab>\t| +)*case[\t| ]*'
                r'((?P<text1>[A-Za-z0-9\(\)_]+)(?P<text1_method>[+-]))*((?P<hex1_start>0x[A-Za-z0-9]+)|(?P<int1_start>[0-9]*))??'
                r'[\t| ]*...[\t| ]*'
                r'((?P<text2>[A-Za-z0-9\(\)_]+)(?P<text2_method>[+-]))*((?P<hex2_start>0x[A-Za-z0-9]+)|(?P<int2_start>[0-9]*))??'
                r'[\t| ]*:(?P<end>\w+)*',
                code
            )
            if (regex):
                data = regex.groupdict()
                print(code[:-1], 'line', index)

                first = None
                end = None
                duo = None
                if data['hex1_start']:
                    first = int(data['hex1_start'], 16)
                elif data['int1_start']:
                    first = int(data['int1_start'], 10)
                else:
                    print('1error id here', index, code)
                if data['hex2_start']:
                    end = int(data['hex2_start'], 16)
                elif data['int2_start']:
                    end = int(data['int2_start'], 10)
                else:
                    print('2error id here', index, code)
                if data['text1']:
                    if data['text1'] == data['text2']:
                        if data['text1_method'] == data['text2_method'] and data['text1_method']:
                            code = '//' + code
                            if first > end:
                                t = first
                                first = end
                                end = t
                            for c in range(first, end + 1):
                                code = data['tab'] + 'case ' + data['text1'] + data['text2_method'] + hex(c) + ' : ' + \
                                       (data['end'] if data['end'] else '') + '\n' + code
                            code = '/*patch start{*/\n' + code + '\n/*patched }end*/'+huakuohao+'\n'
                        else:
                            print('3error id here', index, code)
                    else:
                        print('4error id here', index, code)
                else:
                    code = '//' + code
                    # print(first,end,code)

                    if first > end:
                        t = first
                        first = end
                        end = t
                    for c in range(first, end + 1):
                        code = data['tab'] + 'case ' + hex(c) + ' : ' + (data['end'] if data['end'] else '') + '\n' + code
                    code = '/*patch start{*/\n' + code + '\n/*patched }end*/'+huakuohao+'\n'
            else:
                
                regex = re.match(
                    r'(?P<tab>\t| +)*case[\t| ]*'
                    r'Iop_(?P<iop1>[A-Za-z]+)(?P<bits1>[0-9]*)??'
                    r'[\t| ]*...[\t| ]*'
                    r'Iop_(?P<iop2>[A-Za-z]+)(?P<bits2>[0-9]*)??'
                    r'[\t| ]*:(?P<end>\w+)*',
                    code
                )
                if (regex):
                    data = regex.groupdict()
                    print(code[:-1], 'line', index,data)
                    if data["bits1"] and data["bits1"]=='8' and data["bits2"]=='64' and data["iop1"] and data["iop1"]==data["iop2"]:
                        code = '//' + code
                        for b in [8,16,32,64]:
                            lc=data['tab'] + 'case Iop_' +data['iop1']+ str(b) + ' : ' + (data['end'] if data['end'] else '') + '\n'
                            ##print(lc)
                            code =  lc+ code
                            
                        code = '/*patch start{*/\n' + code + '\n/*patched }end*/\n'
                else:
                    print('5error id here', index, code)            
        if "## args" in code:
            code = code.replace('## args', '__VA_ARGS__')
        elif "##args" in code:
            code = code.replace('##args', '__VA_ARGS__')
        elif "args..." in code:
            code = code.replace('args...', '...')
        elif '__PRETTY_FUNCTION__' in code:
            code = code.replace('__PRETTY_FUNCTION__', '__FUNCSIG__')
        elif '__attribute' in code:
            if k == 0:
                k = 1
                new_code = '''#ifdef _MSC_VER\n#define __attribute__(...)\n#endif\n''' + new_code
        elif "__inline__" in code:
            code = code.replace('__inline__', 'inline')
        
        new_code += code
    # app = '#ifdef _MSC_VER\nchar mydef;\n#endif'
    # while True:
    #     regex = re.compile('([ /\w]+struct[\t| ]*{[\t| ]*\n[ \w*;\n/]*})')
    #     regex = regex.findall(new_code)
    #     if (regex):
    #         if '//' in regex[0].split('\n')[0]:
    #             pass
    #         for r in regex:
    #             d=r.replace(' ','').replace('\t','').split('\n')
    #             if  d[1].startswith( '//' ):
    #
    #     else:
    #         break
    patchedfile.write(new_code)
    patchedfile.close()
