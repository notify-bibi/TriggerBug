import re
import os

code="""sat(define-fun jb20 () (_ BitVec 8)
  #x61)
(define-fun jb24 () (_ BitVec 8)
  #x30)
(define-fun jb8 () (_ BitVec 8)
  #x38)
(define-fun jb23 () (_ BitVec 8)
  #x61)
(define-fun jb25 () (_ BitVec 8)
  #x31)
(define-fun jb31 () (_ BitVec 8)
  #x64)
(define-fun jb28 () (_ BitVec 8)
  #x61)
(define-fun jb22 () (_ BitVec 8)
  #x63)
(define-fun jb16 () (_ BitVec 8)
  #x37)
(define-fun jb5 () (_ BitVec 8)
  #x30)
(define-fun jb21 () (_ BitVec 8)
  #x62)
(define-fun jb11 () (_ BitVec 8)
  #x30)
(define-fun jb26 () (_ BitVec 8)
  #x37)
(define-fun jb29 () (_ BitVec 8)
  #x64)
(define-fun jb30 () (_ BitVec 8)
  #x30)
(define-fun jb6 () (_ BitVec 8)
  #x30)
(define-fun jb1 () (_ BitVec 8)
  #x30)
(define-fun jb2 () (_ BitVec 8)
  #x37)
(define-fun jb14 () (_ BitVec 8)
  #x65)
(define-fun jb17 () (_ BitVec 8)
  #x30)
(define-fun jb10 () (_ BitVec 8)
  #x30)
(define-fun jb18 () (_ BitVec 8)
  #x30)
(define-fun jb9 () (_ BitVec 8)
  #x30)
(define-fun jb27 () (_ BitVec 8)
  #x64)
(define-fun jb7 () (_ BitVec 8)
  #x30)
(define-fun jb3 () (_ BitVec 8)
  #x36)
(define-fun jb13 () (_ BitVec 8)
  #x31)
(define-fun jb15 () (_ BitVec 8)
  #x30)
(define-fun jb12 () (_ BitVec 8)
  #x37)
(define-fun jb19 () (_ BitVec 8)
  #x64)
(define-fun jb0 () (_ BitVec 8)
  #x30)
(define-fun jb4 () (_ BitVec 8)
  #x64)
(define-fun jb32 () (_ BitVec 16)
  #x474a)
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
    print( "".join(["%02x"%(_[1]) for _ in ss] ))
    print("\n\n\n")



print('[patch_byte(addr+i,v) for i,v in enumerate(b)]')



    
 