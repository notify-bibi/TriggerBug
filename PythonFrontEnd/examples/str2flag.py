import re
import os
import sys
if not len(sys.argv)==2:
    print('python ./str2flag.py ""')
    sys.exit(0)
code=sys.argv[1]


"""
python ./str2flag.py "
sat(define-fun p_20 () (_ BitVec 8)
  #x33)
(define-fun p_24 () (_ BitVec 8)
  #x64)
(define-fun p_8 () (_ BitVec 8)
  #x31)
(define-fun p_23 () (_ BitVec 8)
  #x38)
(define-fun p_25 () (_ BitVec 8)
  #x30)
(define-fun p_28 () (_ BitVec 8)
  #x30)
(define-fun p_31 () (_ BitVec 8)
  #x35)
(define-fun p_22 () (_ BitVec 8)
  #x39)
(define-fun p_16 () (_ BitVec 8)
  #x38)
(define-fun p_5 () (_ BitVec 8)
  #x61)
(define-fun p_21 () (_ BitVec 8)
  #x64)
(define-fun p_11 () (_ BitVec 8)
  #x31)
(define-fun p_26 () (_ BitVec 8)
  #x37)
(define-fun p_29 () (_ BitVec 8)
  #x63)
(define-fun p_30 () (_ BitVec 8)
  #x62)
(define-fun p_6 () (_ BitVec 8)
  #x62)
(define-fun p_1 () (_ BitVec 8)
  #x38)
(define-fun p_2 () (_ BitVec 8)
  #x39)
(define-fun p_14 () (_ BitVec 8)
  #x39)
(define-fun p_17 () (_ BitVec 8)
  #x64)
(define-fun p_10 () (_ BitVec 8)
  #x37)
(define-fun p_18 () (_ BitVec 8)
  #x34)
(define-fun p_9 () (_ BitVec 8)
  #x38)
(define-fun p_27 () (_ BitVec 8)
  #x65)
(define-fun p_7 () (_ BitVec 8)
  #x35)
(define-fun p_3 () (_ BitVec 8)
  #x61)
(define-fun p_13 () (_ BitVec 8)
  #x35)
(define-fun p_15 () (_ BitVec 8)
  #x32)
(define-fun p_12 () (_ BitVec 8)
  #x32)
(define-fun p_19 () (_ BitVec 8)
  #x64)
(define-fun p_0 () (_ BitVec 8)
  #x36)
(define-fun p_4 () (_ BitVec 8)
  #x30)
"
"""



rea={}
for c in code.split("define-"):
    c=c.replace("\n","")
    regex = re.match(
                    r'fun (?P<name>[^\(]+)[^#]+'
                    r'#x(?P<end>[a-z0-9_]+)',
                    c
                )
    if (regex):
        data = regex.groupdict()
        rea[data["name"]]=int(data["end"],16)

start=[]
kdict={}
for k in rea:
    regex = re.match(r'\D+',k)
    if (regex):
        data = regex.group()
        if data not in start:
            start.append(data)
            kdict[data]={}
        kdict[data][k] = rea[k]

for s in kdict:
    ss = sorted(kdict[s].items(), key = lambda x:int(x[0].replace(s,"")))
    string = "".join([chr(_[1]) for _ in ss] )
    sl = "".join(["0x%02x, "%(_[1]) for _ in ss])[:-2]
    s2 = "".join(["%02x"%(_[1]) for _ in ss] )
    s3 = ",".join(["0x%02x"%(_[1]) for _ in ss] )
    print("namespace: %-10s len: %d{\n\tchars     : <%s>"%("<%s>"%s, len(ss), string))
    print("\tchars     : <%s>"%("".join([" "+chr(_[1]) for _ in ss] )))
    print("\thexstring = \"%s\""%s2 )
    print("\t"+"%sbuff[%d] = {%s};" %(s, len(ss), s3))
    print("\n}")


if kdict:
    print('[patch_byte(addr+i, ord(v)) for i,v in enumerate(base64.b16decode(hexstring))]')
else:
    print("Incorrect input!!!")



    
 