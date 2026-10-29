import R1Z.PV_RDB2E_ShaScalar
namespace R1Z.PV_RDB2E_ScalarTransport
open Aeneas Aeneas.Std
set_option autoImplicit false
abbrev W := PV_RDB2E_ShaScalar.W

def toWord (x : W) : U32 := ⟨x⟩
def fromWord (x : U32) : W := x.bv

theorem roundtrip (x : U32) : toWord (fromWord x)=x := by cases x; rfl

theorem reverse_roundtrip (x : W) : fromWord (toWord x)=x := rfl

theorem add (x y : W) : U32.wrapping_add (toWord x) (toWord y)=toWord (x+y) := rfl

theorem xor (x y : W) : (toWord x ^^^ toWord y)=toWord (x ^^^ y) := rfl

theorem and (x y : W) : (toWord x &&& toWord y)=toWord (x &&& y) := rfl

theorem or (x y : W) : (toWord x ||| toWord y)=toWord (x ||| y) := rfl

#print axioms roundtrip
#print axioms reverse_roundtrip
#print axioms add
#print axioms xor
#print axioms and
#print axioms or
end R1Z.PV_RDB2E_ScalarTransport
