import re
import os

code="""sat(define-fun flag20 () (_ BitVec 8)
  #x73)
(define-fun flag30 () (_ BitVec 8)
  #x05)
(define-fun flag7 () (_ BitVec 8)
  #x33)
(define-fun flag9 () (_ BitVec 8)
  #x43)
(define-fun flag31 () (_ BitVec 8)
  #x05)
(define-fun flag12 () (_ BitVec 8)
  #x5f)
(define-fun flag19 () (_ BitVec 8)
  #x63)
(define-fun flag28 () (_ BitVec 8)
  #x05)
(define-fun flag22 () (_ BitVec 8)
  #x39)
(define-fun flag6 () (_ BitVec 8)
  #x65)
(define-fun flag10 () (_ BitVec 8)
  #x38)
(define-fun flag27 () (_ BitVec 8)
  #x05)
(define-fun flag3 () (_ BitVec 8)
  #x66)
(define-fun flag4 () (_ BitVec 8)
  #x7b)
(define-fun flag11 () (_ BitVec 8)
  #x63)
(define-fun flag29 () (_ BitVec 8)
  #x05)
(define-fun flag18 () (_ BitVec 8)
  #x4b)
(define-fun flag8 () (_ BitVec 8)
  #x5f)
(define-fun flag1 () (_ BitVec 8)
  #x63)
(define-fun flag25 () (_ BitVec 8)
  #x34)
(define-fun flag26 () (_ BitVec 8)
  #x7d)
(define-fun flag17 () (_ BitVec 8)
  #x70)
(define-fun flag24 () (_ BitVec 8)
  #x64)
(define-fun flag13 () (_ BitVec 8)
  #x49)
(define-fun flag23 () (_ BitVec 8)
  #x61)
(define-fun flag0 () (_ BitVec 8)
  #x73)
(define-fun flag21 () (_ BitVec 8)
  #x37)
(define-fun flag14 () (_ BitVec 8)
  #x32)
(define-fun flag5 () (_ BitVec 8)
  #x41)
(define-fun flag16 () (_ BitVec 8)
  #x5f)
(define-fun flag15 () (_ BitVec 8)
  #x38)
(define-fun flag2 () (_ BitVec 8)
  #x74)
"""


rea={}
for c in code.split("define-fun "):
    c=c.replace("\n","").replace("(","").replace(")","")
    regex = re.match(
                    r'(?P<name>[A-Za-z0-9_]+)[\w _]*#x'
                    r'(?P<end>[a-z0-9_]+)',
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
    if '_' in s:
        continue
    ss=sorted(kdict[s].items(),key=lambda x:int(x[0].replace(s,"")))
    
    dd = [_[1] for _ in ss] 
    string="".join([chr(_[1]) for _ in ss] )
    print(s,len(dd),string)
    sl = "".join(["0x%02x, "%(_[1]) for _ in ss])[:-2]
    print( "b = [%s]"%sl )
    print( "".join(["%02x "%(_[1]) for _ in ss] ))
    print("\n\n\n")



print('[patch_byte(addr+i,v) for i,v in enumerate(b)]')



    
 