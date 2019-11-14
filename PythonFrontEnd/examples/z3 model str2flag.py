import re
import os

code="""sat(define-fun p6 () (_ BitVec 8)
  #xea)
(define-fun p5 () (_ BitVec 8)
  #x98)
(define-fun p1 () (_ BitVec 8)
  #xaa)
(define-fun p2 () (_ BitVec 8)
  #x29)
(define-fun p0 () (_ BitVec 8)
  #x7a)
(define-fun p4 () (_ BitVec 8)
  #x2a)
(define-fun p3 () (_ BitVec 8)
  #x98)
(define-fun p7 () (_ BitVec 8)
  #xab)
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



    
 