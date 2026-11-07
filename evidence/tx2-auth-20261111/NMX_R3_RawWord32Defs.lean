import Aeneas
set_option autoImplicit false
namespace NMX_R3_RawWord32Defs
def encoded (a b c d : BitVec 8) : BitVec 32 := BitVec.fromLEBytes [a,b,c,d]
def assembled (a b c d : BitVec 8) : BitVec 32 :=
 a.setWidth 32 ||| (b.setWidth 32 <<< 8) ||| (c.setWidth 32 <<< 16) ||| (d.setWidth 32 <<< 24)
end NMX_R3_RawWord32Defs
