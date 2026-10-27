import R1Z.PV_B2_Sampler
set_option autoImplicit false
namespace PV_B2_ByteWord
open Aeneas Aeneas.Std

def word (a b c d : U8) : U32 :=
  (UScalar.cast .U32 a) ||| (U32.wrapping_shl (UScalar.cast .U32 b) 8#u32) |||
  (U32.wrapping_shl (UScalar.cast .U32 c) 16#u32) |||
  (U32.wrapping_shl (UScalar.cast .U32 d) 24#u32)

def bits (a b c d : U8) : BitVec 32 :=
  a.bv.setWidth 32 ||| (b.bv.setWidth 32 <<< 8) |||
  (c.bv.setWidth 32 <<< 16) ||| (d.bv.setWidth 32 <<< 24)

theorem machine (a b c d : U8) : word a b c d = (⟨bits a b c d⟩ : U32) := by
  rfl
#print axioms machine
end PV_B2_ByteWord
