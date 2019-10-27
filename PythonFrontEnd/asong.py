#coding:utf-8
import archinfo
import builtins

builtins.TriggerBug_Debug = True
import TriggerBug
from TriggerBug.z3  import *

# print s
var1 =  ZeroExt(24, BitVec('var1 ', 8))
var2 =  ZeroExt(24, BitVec('var2 ', 8))
var3 =  ZeroExt(24, BitVec('var3 ', 8))
var4 =  ZeroExt(24, BitVec('var4 ', 8))
var5 =  ZeroExt(24, BitVec('var5 ', 8))
var6 =  ZeroExt(24, BitVec('var6 ', 8))
var7 =  ZeroExt(24, BitVec('var7 ', 8))
var8 =  ZeroExt(24, BitVec('var8 ', 8))
var9 =  ZeroExt(24, BitVec('var9 ', 8))
var10 = ZeroExt(24, BitVec('var10', 8))
var11 = ZeroExt(24, BitVec('var11', 8))
var12 = ZeroExt(24, BitVec('var12', 8))
var13 = ZeroExt(24, BitVec('var13', 8))
var14 = ZeroExt(24, BitVec('var14', 8))
var15 = ZeroExt(24, BitVec('var15', 8))
var16 = ZeroExt(24, BitVec('var16', 8))
var17 = ZeroExt(24, BitVec('var17', 8))
var18 = ZeroExt(24, BitVec('var18', 8))
var19 = ZeroExt(24, BitVec('var19', 8))
var20 = ZeroExt(24, BitVec('var20', 8))
var21 = ZeroExt(24, BitVec('var21', 8))
var22 = ZeroExt(24, BitVec('var22', 8))
var23 = ZeroExt(24, BitVec('var23', 8))
var24 = ZeroExt(24, BitVec('var24', 8))
var25 = ZeroExt(24, BitVec('var25', 8))
var26 = ZeroExt(24, BitVec('var26', 8))
var27 = ZeroExt(24, BitVec('var27', 8))
var28 = ZeroExt(24, BitVec('var28', 8))
var29 = ZeroExt(24, BitVec('var29', 8))
var30 = ZeroExt(24, BitVec('var30', 8))
var31 = ZeroExt(24, BitVec('var31', 8))
var32 = ZeroExt(24, BitVec('var32', 8))

# var1 = Int('var1')
# var2 = Int('var2')
# var3 = Int('var3')
# var4 = Int('var4')
# var5 = Int('var5')
# var6 = Int('var6')
# var7 = Int('var7')
# var8 = Int('var8')
# var9 = Int('var9')
# var10 = Int('var10')
# var11 = Int('var11')
# var12 = Int('var12')
# var13 = Int('var13')
# var14 = Int('var14')
# var15 = Int('var15')
# var16 = Int('var16')
# var17 = Int('var17')
# var18 = Int('var18')
# var19 = Int('var19')
# var20 = Int('var20')
# var21 = Int('var21')
# var22 = Int('var22')
# var23 = Int('var23')
# var24 = Int('var24')
# var25 = Int('var25')
# var26 = Int('var26')
# var27 = Int('var27')
# var28 = Int('var28')
# var29 = Int('var29')
# var30 = Int('var30')
# var31 = Int('var31')
# var32 = Int('var32')

def shl(a,b):
    return a*pow(2,b)

flag=   And((48 * var31 + 174 * var32 + 111 * var2 + 108 * var1 + 92 * var3 + 194 * var4 + 124 * var5 + 240 * var6 + 126 * var7 + 81 * var8 + 144 * var9 + 103 * var10 + 161 * var11 + 50 * var12 + 67 * var13 + 15 * var14 + 127 * var15 + 232 * var16 + 188 * var17 + 19 * var18 + 233 * var19 + 153 * var20 + 231 * var21 + 40 * var22 + 112 * var23 + 106 * var24 + 135 * var25 + 90 * var26 + 67 * var27 + 20 * var28 + 248 * var29 + 45 * var30 == 359512) ,
        (13 * var31 + 101 * var32 + 78 * var2 + 227 * var1 + 195 * var3 + 81 * var4 + 10 * var5 + 248 * var6 + 186 * var7 + 171 * var8 + 148 * var9 + 194 * var10 + 40 * var11 + 180 * var12 + 17 * var13 + 212 * var14 + 104 * var15 + 90 * var16 + 178 * var17 + 26 * var18 + 225 * var19 + 209 * var20 + 32 * var21 + 169 * var22 + 94 * var23 + 156 * var24 + 154 * var25 + 56 * var26 + 244 * var27 + 149 * var28 + 120 * var29 + 131 * var30 == 387514) ,
        (240 * var31 + 53 * var32 + 44 * var2 + 83 * var1 + 95 * var3 + 131 * var4 + 30 * var5 + 55 * var6 + 46 * var7 + 36 * var8 + 67 * var9 + 109 * var10 + 69 * var11 + 8 * var13 + 248 * var14 + 40 * var15 + 154 * var16 + 86 * var18 + 251 * (var17 + var12) + 112 * var19 + 9 * var20 + 174 * var21 + 197 * var22 + 38 * var23 + 14 * var24 + 202 * var25 + 60 * var26 + 117 * var27 + 188 * var28 + 136 * var29 + 145 * var30 == 301487) ,
        (234 * (var31 + var18) + 25 * (var32 + var30) + 162 * var2 + 152 * var1 + 112 * var3 + 57 * var4 + 102 * var5 + 182 * var6 + 10 * var7 + 139 * var8 + 30 * var9 + 7 * var10 + 145 * var11 + 127 * var12 + 148 * var13 + 5 * var14 + 165 * var15 + 109 * var16 + 110 * var17 + 113 * var19 + 33 * var20 + 192 * var21 + 45 * var22 + 65 * var23 + 105 * var24 + 140 * var25 + 116 * var26 + 35 * var27 + 48 * var28 + 155 * var29 == 296549) ,
        (82 * var31 + 113 * var32 + 189 * var2 + 101 * var1 + 236 * var3 + 118 * var4 + 141 * var5 + 148 * var6 + 197 * var7 + 7 * var8 + 104 * var10 + 45 * var11 + 130 * var12 + 39 * var13 + 164 * var14 + 88 * var15 + 241 * var16 + 107 * var18 + 108 * (var17 + var9) + 76 * var19 + 34 * var20 + 210 * var21 + 29 * var22 + 156 * var23 + 90 * var24 + 139 * var25 + 151 * var26 + 10 * var27 + 97 * var28 + 209 * var29 + 46 * var30 == 344514) ,
        (179 * var31 + 72 * (var32 + var17) + 13 * var2 + 182 * var1 + 50 * var3 + 102 * var4 + 155 * var5 + 230 * var6 + 3 * var7 + 225 * var8 + 237 * var9 + 163 * var10 + 38 * var11 + 176 * var12 + 115 * var13 + 105 * var14 + 203 * var15 + 26 * var16 + 111 * var18 + 96 * var19 + 240 * var20 + 139 * var21 + 117 * var22 + 153 * var23 + 120 * var24 + 151 * var25 + 25 * var26 + 49 * var27 + 90 * var28 + 98 * var29 + 7 * var30 == 346892) ,
        (156 * var31 + 61 * var32 + 150 * var2 + 170 * var1 + 110 * var5 + 99 * var6 + 127 * var7 + 101 * (var8 + var4) + 203 * var9 + 209 * var10 + 100 * var12 + 226 * (var13 + var3) + 186 * var14 + 252 * var15 + 39 * var16 + 65 * var17 + 67 * var18 + 225 * var19 + 174 * var20 + var21 + 214 * var23 + 187 * (var22 + var11) + 22 * var24 + 74 * var25 + 99 * var26 + 129 * var27 + 254 * var28 + 13 * var29 + 97 * var30 == 386678) ,
        (154 * var31 + 117 * var32 + 88 * var2 + var1 + 118 * var3 + 232 * var4 + 60 * var5 + 252 * var6 + 133 * var7 + 177 * var8 + 185 * var9 + 222 * var10 + 32 * var11 + 48 * var12 + var13 + 242 * var14 + 240 * var15 + 218 * var16 + 81 * var17 + 22 * var18 + 73 * var19 + 171 * var20 + 139 * var21 + 72 * var22 + 106 * var23 + 62 * var24 + 156 * var25 + 134 * var26 + 220 * var27 + 19 * var28 + 77 * var29 + 94 * var30 == 348667) ,
        (220 * var31 + 151 * var32 + 173 * var2 + 189 * var1 + 41 * var3 + 39 * var4 + 26 * var5 + 232 * var6 + 75 * var7 + 75 * var8 + 95 * var9 + 7 * var10 + 117 * var11 + 96 * var12 + 211 * var13 + 130 * var14 + 228 * var15 + 143 * var16 + 91 * var17 + 247 * var18 + 43 * var19 + 122 * var20 + 131 * var21 + 52 * var22 + 48 * var23 + 29 * var24 + 111 * var25 + 38 * var26 + 19 * var27 + 242 * var28 + 162 * var29 + 70 * var30 == 316884) ,
        (231 * var31 + 92 * var32 + 136 * var2 + 236 * var1 + 147 * var3 + 104 * var4 + 79 * var5 + 204 * var6 + 220 * var7 + 25 * var8 + 38 * var9 + 233 * var10 + 165 * var11 + 20 * var12 + 174 * var13 + 120 * var14 + 214 * var15 + 18 * var16 + 233 * var17 + 119 * var18 + 244 * var19 + 143 * var20 + 126 * var21 + 226 * var22 + 77 * var23 + 33 * var24 + 189 * var25 + 5 * var26 + 150 * var27 + 160 * var28 + 14 * var29 + 112 * var30 == 372620) ,
        (50 * var31 + 203 * var32 + 38 * var2 + 191 * var1 + 193 * var3 + 250 * var4 + 212 * var5 + 175 * var6 + 39 * var7 + 94 * var8 + 183 * var9 + 172 * var10 + 171 * var11 + 163 * var12 + 129 * var13 + 165 * var14 + shl(var15 , 6) + 170 * var16 + 199 * var17 + 167 * var19 + 216 * var21 + 2 * (var20 + var18) + 252 * var22 + 184 * var23 + 187 * var24 + 97 * var25 + 109 * var26 + 98 * var27 + 135 * var28 + 192 * var29 + 88 * var30 == 413102) ,
        (43 * var31 + 196 * var32 + 81 * var2 + 203 * var1 + 252 * var3 + 104 * var4 + 248 * var5 + 156 * var6 + 199 * var7 + 46 * var8 + 240 * var10 + 149 * var11 + 155 * var12 + 102 * var13 + 95 * var14 + 51 * var15 + 62 * var18 + 58 * var19 + 208 * (var16 + var9 + var17) + 117 * var20 + 72 * var21 + 23 * var22 + 193 * var23 + 193 * var24 + 226 * var25 + 217 * var26 + 106 * var27 + 147 * var28 + 136 * var29 + 16 * var30 == 428661) ,
        (80 * var31 + 49 * var32 + 69 * var2 + 144 * var1 + 224 * var3 + 107 * var4 + 225 * var5 + 83 * var6 + 15 * var7 + 10 * var8 + 214 * var9 + 152 * var10 + 24 * var11 + 136 * var12 + 165 * var13 + 208 * var14 + 38 * var15 + 67 * var16 + 201 * var17 + 180 * var18 + 158 * var19 + 75 * var20 + 111 * var21 + 65 * var22 + 211 * var23 + 220 * var24 + 135 * var25 + 125 * var26 + 216 * var27 + 105 * var28 + 122 * var29 + 112 * var30 == 371484) ,
        (76 * var31 + 129 * var32 + 68 * var2 + 143 * var1 + 127 * var3 + 51 * var4 + 88 * var6 + 153 * var7 + 9 * var8 + 149 * var9 + 107 * var10 + 178 * var11 + 166 * var12 + 190 * var13 + 177 * var14 + 99 * var15 + 71 * var16 + 63 * var17 + 233 * var18 + 58 * var19 + 132 * var20 + 109 * var21 + 75 * var22 + 95 * var24 + 152 * (var23 + var5) + 74 * var25 + 195 * var26 + 90 * var27 + 251 * var28 + 205 * var29 + 8 * var30 == 350848) ,
        (31 * var31 + 102 * var32 + 146 * var2 + 209 * var1 + 59 * var3 + 38 * var4 + 40 * var5 + 56 * var6 + 182 * var7 + 245 * var8 + 67 * var9 + 202 * var10 + 177 * var11 + 26 * var13 + 126 * var14 + 161 * var15 + 95 * var16 + 133 * var17 + 123 * var18 + 163 * var19 + 30 * var20 + 88 * var21 + 219 * var22 + 5 * var23 + 86 * var24 + 156 * var26 + 183 * (var25 + var12) + 253 * var27 + 97 * var28 + 43 * var29 + shl(var30 , 7) == 334408) ,
        (91 * var31 + 136 * var32 + 223 * var2 + 146 * var1 + 137 * var3 + 228 * var4 + 226 * var5 + 155 * var6 + 170 * var7 + 92 * var8 + 77 * var9 + 17 * var10 + 22 * var11 + shl(var12 , 7) + 20 * var13 + 171 * var14 + 142 * var15 + 170 * var16 + 192 * var17 + 49 * var18 + 200 * var19 + 178 * var20 + 154 * var21 + 42 * var22 + 5 * var23 + 159 * var24 + 251 * var25 + 152 * var26 + 7 * var27 + 247 * var28 + 145 * var29 + 39 * var30 == 382822) ,
        (121 * var31 + 205 * (var32 + var8) + 204 * var2 + 169 * var1 + 244 * var3 + 26 * var4 + 77 * var5 + 134 * var6 + 221 * var7 + 149 * var9 + 47 * var10 + var11 + 197 * var12 + 82 * var13 + 195 * var14 + 123 * var15 + 219 * var16 + 116 * var17 + 80 * var18 + 13 * var19 + 231 * var20 + 173 * var21 + 192 * var22 + 220 * var23 + 224 * var24 + 108 * var25 + 104 * var26 + 56 * var27 + 152 * var28 + 84 * var29 + 226 * var30 == 420160) ,
        (73 * var31 + 95 * var32 + 45 * var2 + 184 * var1 + 176 * var3 + 161 * var6 + 142 * var7 + 171 * var8 + 215 * var9 + 83 * var10 + 233 * var11 + 184 * var12 + 171 * var13 + 182 * var14 + 126 * (var15 + var4) + 111 * var16 + 118 * (var17 + var5) + 67 * var18 + 92 * var19 + 219 * var20 + 70 * var21 + 252 * var22 + 194 * var23 + 21 * var24 + 245 * var25 + 204 * var26 + 48 * var27 + 150 * var28 + 39 * var29 + 85 * var30 == 402263) ,
        (170 * var31 + 120 * var32 + 224 * var2 + 48 * var1 + 164 * var3 + 138 * var4 + 92 * var5 + 3 * var6 + 191 * var7 + 94 * var8 + 19 * var9 + 50 * var10 + 34 * var11 + 167 * var12 + 75 * var13 + 72 * var14 + 238 * var15 + 15 * var16 + 111 * var17 + 216 * var18 + 84 * var19 + 40 * var20 + 145 * var21 + 112 * var22 + 140 * var23 + 204 * var24 + 154 * var25 + 195 * var26 + 175 * var27 + 250 * var28 + 202 * var29 + 169 * var30 == 366968) ,
        (170 * var31 + 68 * var32 + 189 * var3 + 112 * var1 + 50 * var4 + 247 * var5 + 240 * var6 + 164 * var7 + 5 * var8 + 139 * var9 + 56 * var10 + 19 * (var11 + var2) + 4 * var12 + 23 * var13 + 96 * var15 + 254 * var16 + 63 * var17 + 247 * var18 + 149 * var19 + 183 * var20 + shl(var21 , 7) + 147 * var22 + 213 * var23 + 243 * var24 + 172 * (var25 + var14) + 144 * var26 + 246 * var27 + 25 * var28 + 106 * var29 + 176 * var30 == 384909) ,
        (31 * var32 + 41 * (var31 + var25) + 22 * var2 + 184 * var1 + 183 * var3 + shl(var4 , 7) + 149 * var5 + 227 * var7 + 113 * var8 + 65 * var9 + 159 * var10 + 74 * var11 + 170 * var12 + 186 * var13 + 174 * (var14 + var6) + 211 * var15 + var16 + 156 * var18 + 253 * var19 + 223 * (var20 + var17) + 241 * var21 + 252 * var22 + 148 * var23 + 93 * var24 + 125 * var26 + 27 * var27 + 136 * var28 + 78 * var29 + 248 * var30 == 425203) ,
        (82 * var31 + 39 * var32 + 237 * var2 + 155 * var1 + 242 * var3 + 145 * var5 + 99 * var6 + 239 * var7 + 3 * var9 + 43 * var10 + 46 * var11 + 155 * var12 + 208 * var13 + 75 * var14 + 181 * var16 + 197 * var17 + 140 * (var18 + var15) + 10 * (var19 + var4) + 170 * var20 + 142 * var21 + 212 * var22 + 186 * var23 + 27 * var24 + 105 * (var25 + var8) + 118 * var26 + 198 * var27 + 243 * var28 + 13 * var29 + 113 * var30 == 372162) ,
        (50 * var32 + 136 * (var31 + var24) + 206 * var2 + 207 * var1 + 127 * var3 + 58 * var4 + 91 * var5 + 7 * var7 + 17 * var8 + 63 * var9 + 180 * var10 + 40 * var11 + 96 * var12 + 202 * var13 + 185 * var14 + 68 * var15 + 72 * var16 + 240 * var17 + 36 * var18 + 139 * var19 + 199 * var20 + 76 * var21 + 229 * var22 + 159 * var23 + 94 * var25 + 19 * var26 + 3 * var27 + 45 * var29 + 87 * (var28 + var6) + 6 * var30 == 297509) ,
        (90 * var31 + 12 * var32 + 215 * var2 + 115 * var1 + 40 * var3 + 166 * var4 + 87 * var5 + 83 * var6 + 74 * var7 + 202 * var8 + 149 * var10 + 114 * var11 + 76 * var12 + 204 * var13 + 218 * var14 + 63 * var15 + 123 * var16 + 9 * var17 + 172 * var18 + 38 * var19 + 138 * var20 + 35 * var21 + 200 * var22 + 221 * var23 + 144 * var24 + 108 * var26 + var27 + 235 * (var25 + var9) + 245 * var28 + 153 * var29 + 184 * var30 == 372215) ,
        (114 * var31 + 36 * var32 + 190 * var2 + 123 * var1 + 55 * var3 + 180 * var4 + 84 * var5 + 231 * var6 + 81 * var7 + 116 * var8 + 61 * var9 + 3 * var10 + 94 * var11 + 190 * var13 + 187 * var14 + 142 * var15 + 62 * var16 + 225 * var17 + 240 * var18 + 179 * var19 + 150 * var20 + 77 * var21 + 196 * var23 + 85 * (var22 + var12) + 12 * var24 + 144 * var25 + 122 * var26 + 28 * var27 + 224 * var28 + 248 * var29 + 143 * var30 == 370337) ,
        (190 * var31 + 122 * (var32 + var12) + 202 * var2 + 2 * var1 + 40 * var3 + 224 * var4 + 154 * var5 + 65 * var6 + 241 * var8 + 13 * var9 + 213 * var10 + 176 * var11 + 30 * (var13 + var7) + 14 * var15 + 191 * var16 + 80 * var17 + 116 * var18 + 74 * var19 + 70 * var20 + 32 * var21 + 189 * var22 + 76 * var23 + 95 * var24 + 103 * var26 + 158 * (var25 + var14) + 7 * var27 + 201 * var28 + 204 * var29 + 91 * var30 == 314564) ,
        (5 * var31 + 176 * var32 + 154 * var2 + 42 * var1 + 223 * var3 + 165 * var4 + 155 * var5 + 101 * var6 + 75 * var7 + 95 * var8 + 253 * var9 + 14 * var10 + 158 * var11 + 199 * var12 + 110 * var13 + 89 * var14 + 205 * var15 + 202 * var16 + 162 * var18 + 67 * var19 + 30 * var20 + 115 * var21 + 27 * var23 + 83 * (var22 + var17) + 31 * var24 + 118 * var25 + 160 * var26 + 248 * var27 + 66 * var28 + 88 * var29 + 44 * var30 == 325974) ,
        (84 * var32 + 125 * (var31 + var17) + 168 * var2 + 34 * var1 + 160 * var4 + 243 * var5 + 41 * var6 + 146 * var7 + 62 * var9 + 235 * var10 + 185 * var11 + 180 * var12 + 10 * var13 + 150 * var14 + 140 * var16 + 114 * var18 + 35 * var19 + 34 * var20 + 38 * var21 + 123 * var22 + 163 * var23 + 5 * var25 + 208 * (var24 + var15) + 29 * (var26 + var8) + 207 * var27 + 111 * var28 + 72 * (var29 + var3) + 65 * var30 == 307088) ,
        (140 * var31 + 197 * var32 + 11 * var2 + 18 * var1 + 175 * var4 + 44 * var5 + shl(var6 , 7) + 32 * var7 + 100 * var8 + 116 * var10 + 253 * var11 + 213 * var12 + 67 * var13 + 16 * var14 + 171 * var15 + 178 * var16 + 7 * var18 + 162 * var19 + 152 * var20 + 78 * var21 + 167 * var22 + 177 * var23 + 97 * (var24 + var17) + 26 * (var25 + var3) + 155 * var26 + 127 * var27 + 21 * (var28 + var9) + 243 * var29 + 188 * var30 == 322340) ,
        (152 * var31 + 7 * (var32 + var28) + 110 * var2 + 140 * var1 + 164 * var3 + 208 * var4 + 72 * var5 + 113 * var6 + 9 * var7 + 47 * var8 + 179 * var9 + 166 * var10 + 51 * var11 + 34 * var12 + 91 * var13 + 184 * var14 + 89 * var15 + 162 * var16 + 233 * var17 + 156 * var19 + 244 * var21 + 127 * (var20 + var18) + 183 * var22 + 193 * var23 + 138 * var24 + 242 * var25 + 90 * var26 + 193 * var27 + 252 * var29 + 113 * var30 == 380716) ,
        (197 * var31 + 75 * (var32 + var3) + 105 * var2 + 133 * var1 + 146 * var4 + 173 * var5 + 27 * var6 + 97 * var7 + 142 * var8 + 164 * var9 + 15 * var10 + 10 * var11 + 177 * var12 + 239 * var13 + 141 * var14 + 189 * var15 + 67 * var16 + 153 * var17 + 108 * var18 + 206 * var19 + 210 * var20 + 171 * var21 + 252 * var22 + 84 * var23 + 249 * var24 + 7 * var25 + 168 * var26 + 100 * var27 + 30 * var28 + 196 * var29 + 244 * var30 == 393331) ,
        (53 * var31 + 79 * var32 + 221 * var2 + 147 * var1 + 57 * var3 + 186 * var4 + 69 * var5 + 230 * var6 + 167 * var7 + 3 * var8 + 220 * var9 + 63 * var10 + 235 * var12 + 156 * var13 + 146 * var14 + 75 * var15 + 198 * var16 + 204 * var17 + 197 * var18 + 59 * var19 + 61 * var20 + 179 * var21 + 47 * var22 + 221 * var23 + 127 * var24 + 210 * var25 + 241 * var27 + 218 * (var26 + var11) + 135 * var28 + 196 * var29 + 185 * var30 == 430295));




slove = Solver()
slove.add(flag)
print("dfgvdfgdfgdfgfdgdfgdfg")
if slove.check() == sat:
    m=slove.model()
    print(m)

#
# def decode2():
#     de=[]
#
#     args = ['rdi','rsi','rdx','rcx','r8']
#     def chk2(_state):
#         gh=_state.dh
#         re=TriggerBug.eval_all(_state, gh)
#         print("success    ",  re )
#         return TriggerBug.Running
#
#     def evalvalue(_state):
#         addr=_state.rdi
#         _state.solver.push()
#         for i,v in enumerate(c):
#             val=_state.mem_r(addr+i,1)
#             if(type(val)==int):
#                 print(val)
#                 if(val!=v):
#                     return TriggerBug.Death
#             else:
#                 _state.solver.add(val==v)
#         if (_state.solver.check()==z3.sat):
#             m=_state.solver.model()
#             print("success    ")
#
#             for a in args:
#                 k = z3.BitVec(a, 64, top_state.ctx)
#                 de.append(m.eval(k).as_long())
#             _state.solver.pop()
#             return TriggerBug.Death
#         else:
#             print("faild    ")
#             _state.solver.pop()
#             return TriggerBug.Death
#
#
#     top_state=TriggerBug.TopState(
#         file_name=r'./TriggerBug-asong.xml',
#         need_record=True,#在需要合并(compress)state时，必须要保证被compress 的state对象的need_record=True，否则会报错，因为need_record=False的state是不会记录子state生命周期中所产生的修改,继而无法合并
#         oep=0,
#         Ijk_unsupport_call=None,#if set,Ir jump kind call what I not support will call this func
#         Ijk_hook_call=None#if set, all the Ir jump kind call will call this func
#     )
#
#     # state.mem_write(0x7ffff7dec7b8,0x90909090,4)
#     # state.mem_write(0x7ffff7dec7b8+4,0x90,1)
#     # state.mem_write(0x7FFFF7DEC7D4,0x90909090,4)
#     # state.mem_write(0x7FFFF7DEC7D4+4,0x90,1)
#     #
#     # arg0 = state.rdi
#     # arg1 = state.rsi
#     # arg2 = state.rdx
#     # arg3 = state.rcx
#     # arg4 = state.r8
#     #
#     # for i,a in enumerate(args):
#     #     k = z3.BitVec(a, 64, state.ctx)
#     #     state.add(z3.UGT(k, 0) , True)
#     #     state.regs_write(a, k)
#     #     if(i<4):
#     #         index=state.mem_r(state.rbp - 0x148,1)
#     #         addr=state.rbp-0x140+(index+i)*8
#     #         state.mem_w(addr,k,8)
#
#     top_state.go()
#     top_state.wait()
#     print(top_state)
#
#     return  de
# dec2=None
# if 1:
#     dec2 = decode2()
# else:
#     dec2=[288230377917403225, 1152921508689107638, 17594813653004, 70372930466384, 382056768]
#

#
#
#
#
#
#
#
#
#
# def faild(_state):
#     return Death
#
# def fcmp(_state):
#     return 88
#
# def cmp2(_state):
#     return 99
#
# flagcount=0
#
# m=None
# def success(_state):
#     global m
#     print(_state.solver.check())
#     m=_state.solver.model()
#     print(m)
#     return 100
#
# addr=None
#
#
# def IDIV(_state):
#     d=_state.rax // _state.ecx
#     m=_state.rax % _state.ecx
#     _state.regs_write('rax',d)
#     _state.regs_write('rdx',m)
#     return 99
#
# def sprintf(_state):
#     value=_state.edx
#     print("sprintf",value)
#     saddr=_state.rdi
#     hi=z3.ZeroExt(4,z3.Extract(7,4,value))
#     hi=z3.If(hi<10,hi +ord('0'),hi+(ord('A')-10),_state.ctx)
#
#
#     lo=z3.ZeroExt(4,z3.Extract(3,0,value))
#     lo=z3.If(lo<10,lo +ord('0'),lo+(ord('A')-10),_state.ctx)
#     _state.mem_w(saddr,lo,1)
#     _state.mem_w(saddr+1, hi, 1)
#     return Running
# def strlen(_state):
#     _state.reg_w('rax',16*2)
#     return Running
#
#
#
# def strcmp(_state):
#     c=b'RVYtG85NQ9OPHU4uQ8AuFM+MHVVrFMJMR8FuF8WJQ8Y='
#     addr=_state.rdi
#     _state.solver.push()
#     for i,v in enumerate(c):
#         val=_state.mem_r(addr+i,1)
#
#         if(type(val)==int):
#             if(val!=v):
#                 return Death
#         else:
#             print(type(val),chr(val.as_long()), chr(v))
#             _state.solver.add(val==v)
#     if (_state.solver.check()==z3.sat):
#         m=_state.solver.model()
#         print("success    ",m)
#         _state.solver.pop()
#         return Running
#     else:
#         print("faild    ")
#         _state.solver.pop()
#         return Death
#
#
# # sss=z3.BitVec("flag", 8, state.ctx )
# # state.regs_write("al",sss)
# # fg=state.regs_read("al")
# # del fg
# # ssjk=state.rbp-0x40
#
#
# addr=state.rbp-0x80
#
# n=8
# for i in range(n):
#     k=z3.BitVec('flag_%d' % (i+50), 8, state.ctx)
#     so1=z3.And( k >= ord("A"), k <= ord("Z"),state.ctx)
#     so2=z3.And( k >= ord("a"), k <= ord("z"), state.ctx)
#     so3=z3.And( k >= ord("0"), k <= ord("9"), state.ctx)
#     state.add(z3.Or(so1, so2,so3,state.ctx) == True, True)
#     state.mem_write(addr+i,k,1)
#
#
#
#
#
# state.hook_add(0X0406B24  ,success)
# state.hook_add(0X0406B3A   ,faild)
#
# state.hook_add(0x4066EB     ,fcmp)
#
#
# def chk(_state):
#     dl=_state.dl
#     saddr=_state.rbp-0x70
#     for m in range(20):
#         print("check",z3.simplify(_state.mem_r(saddr+m,1)))
#     # print("check", _state.rax,z3.simplify(dl))
#     # _state.mem_w(_state.rax,_state.dl,1)
#     return Running
#
#
# #
# # state.mem_write(0x0000401938 ,0x9090   ,2)
# # state.hook_add(0x00004069E2   ,chk)
# #
#
#
#
#
# state.hook_add(0x0040680C    ,sprintf)
# state.mem_write(0x00406969 ,0x90909090   ,4)
# state.mem_write(0x00406969+4 ,0x90   ,1)
#
# state.hook_add(0x0000406AAC     ,strlen)
#
# state.hook_add(0x04067A7   ,cmp2)
#
# # state.hook_add(0x000040954E       ,okk)
# # # state.hook_add(0x00435087 ,IDIV)
# #
# # print(state.mem_w(5019890,7,1))
#
# def getNewState(_state):
#     if(_state.branch):
#         return False
#     for i in _state.branch:
#         if i.status==Fork:
#             if(getNewState(i)):
#                 return True
#     return False
#
#
#
# stateGo(state)
#
#
# for i in range(7):
#     stateGo(state)
#     print(i,state)
#     state.compress(0x004066EB,88,[Death])
#     print(i,state)
#
# stateGo(state)
# print(state)
# state.compress(0x04067A7,99,[Death])
# print(state)
#
# stateGo(state)
# print(state)
#
# #
# # while True:
# #     stateGo(state)
# #     print(state)
# #     if(state.status==Death):
# #         break
# #     elif state.status==Fork:
# #         print('fork')
# #     if state.branch:
# #         state.compress(0x00406A75,88,[Death])
# #         print(state.rax)
# #         if(isinstance(state.rax,z3.ExprRef)):
# #             rax=z3.simplify(state.rax)
# #             print(rax)
# #             re=eval_all(state,rax)
# #             print(re)
# #         if state.status == Fork:
# #             print('fork')
# #             state=getNewState(state)
#
#
# #print(state)
# # state.compress(0x00400ECD,100,[Death])
# #print(state,addr)
# # state=state.branch[0x400ecd]
# #state.hook_add(0x00400ECD  ,nasjk)
# print(m)