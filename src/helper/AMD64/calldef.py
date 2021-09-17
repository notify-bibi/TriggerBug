for op in "ADD ADC SUB SBB LOGIC INC DEC SHL SHR ROL ROR ANDN BLSI BLSMSK BLSR UMUL SMUL".split(" "):
    for i,v in enumerate( ["cf", "pf", "af", "zf", "sf", "of"]):
        dd=["NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO"]
        dd[i]="MACRO"
        print("#define ACTIONS_"+op+"_"+v+("(A, B) ACTIONS_"+op+"({}, {}, {}, {}, {}, {}, A, B)	".format(*dd)))

op="ADX"
for i,v in enumerate( ["cf", "pf", "af", "zf", "sf", "of"]):
        dd=["NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO"]
        dd[i]="MACRO"
        print("#define ACTIONS_"+op+"_"+v+("(A, B, C) ACTIONS_"+op+"({}, {}, {}, {}, {}, {}, A, B, C)	".format(*dd)))
        
for op in "UMUL SMUL".split(" "):    
    for i,v in enumerate( ["cf", "pf", "af", "zf", "sf", "of"]):
        dd=["NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO","NOTEMACRO"]
        dd[i]="MACRO"
        print("#define ACTIONS_"+op+"_"+v+("(A, B, C, D, E) ACTIONS_"+op+"({}, {}, {}, {}, {}, {}, A, B, C, D, E)	".format(*dd)))