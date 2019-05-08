import re
import os

from collections import OrderedDict


code="""sat(define-fun flag20 () (_ BitVec 8)
  #x3a)
(define-fun flag30 () (_ BitVec 8)
  #x3a)
(define-fun flag7 () (_ BitVec 8)
  #x3c)
(define-fun flag9 () (_ BitVec 8)
  #x2c)
(define-fun flag31 () (_ BitVec 8)
  #x3a)
(define-fun flag33 () (_ BitVec 8)
  #x3a)
(define-fun flag12 () (_ BitVec 8)
  #x3c)
(define-fun flag19 () (_ BitVec 8)
  #x3a)
(define-fun flag34 () (_ BitVec 8)
  #x3a)
(define-fun flag35 () (_ BitVec 8)
  #x3a)
(define-fun flag32 () (_ BitVec 8)
  #x3a)
(define-fun flag28 () (_ BitVec 8)
  #x3a)
(define-fun flag22 () (_ BitVec 8)
  #x3a)
(define-fun flag36 () (_ BitVec 8)
  #x3a)
(define-fun flag6 () (_ BitVec 8)
  #x3c)
(define-fun flag10 () (_ BitVec 8)
  #x3c)
(define-fun flag27 () (_ BitVec 8)
  #x3a)
(define-fun flag3 () (_ BitVec 8)
  #x5a)
(define-fun flag4 () (_ BitVec 8)
  #x5a)
(define-fun flag11 () (_ BitVec 8)
  #x3c)
(define-fun flag29 () (_ BitVec 8)
  #x3a)
(define-fun flag18 () (_ BitVec 8)
  #x3c)
(define-fun flag8 () (_ BitVec 8)
  #x3c)
(define-fun flag1 () (_ BitVec 8)
  #x5c)
(define-fun flag25 () (_ BitVec 8)
  #x3a)
(define-fun flag26 () (_ BitVec 8)
  #x3a)
(define-fun flag17 () (_ BitVec 8)
  #x3c)
(define-fun flag24 () (_ BitVec 8)
  #x3a)
(define-fun flag13 () (_ BitVec 8)
  #x3c)
(define-fun flag23 () (_ BitVec 8)
  #x3a)
(define-fun flag0 () (_ BitVec 8)
  #x1a)
(define-fun flag21 () (_ BitVec 8)
  #x3a)
(define-fun flag14 () (_ BitVec 8)
  #x3c)
(define-fun flag5 () (_ BitVec 8)
  #x3c)
(define-fun flag16 () (_ BitVec 8)
  #x3c)
(define-fun flag37 () (_ BitVec 8)
  #x3a)
(define-fun flag15 () (_ BitVec 8)
  #x3c)
(define-fun flag2 () (_ BitVec 8)
  #x5a)
"""
rea={}
for c in  code.split("(define-fun "):
    c=c.replace("\n","").replace("(","").replace(")","")
    regex = re.match(
                    r'(?P<name>[A-Za-z0-9_]+)[\w _]*#x'
                    r'(?P<end>[a-z0-9_]+)',
                    c
                )
    if (regex):
        data = regex.groupdict()
        rea[data["name"]]=int(data["end"],16)
    
print(rea)

def sortedDictValues1(adict): 
    return 
ss=sorted(rea.items(),key=lambda x:int(x[0].replace("flag","")))
print(ss)

print( "".join([chr(_[1]) for _ in ss] ))





    
 