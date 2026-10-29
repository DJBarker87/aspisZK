import R1Z.PV_CBL_ShaCount
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaBitLength
set_option autoImplicit false

/-- Arithmetic subexpression of sha2 0.10.9 core_api.rs finalization in the
frozen release wrapping profile; padding/compression binding is still open. -/
def bitLength (pos : Usize) (blocks : U64) : U64 :=
  U64.wrapping_mul 8#u64
    (U64.wrapping_add (UScalar.cast .U64 pos) (U64.wrapping_mul 64#u64 blocks))

theorem value (pos : Usize) (blocks : U64) :
    (bitLength pos blocks).val = (8*(pos.val+64*blocks.val))%2^64 := by
  simp only [bitLength,U64.wrapping_mul_val_eq,U64.wrapping_add_val_eq,
    PV_CBL_ShaCount.cast_count,UScalar.size,UScalarTy.numBits]
  change (8*((pos.val+(64*blocks.val)%2^64)%2^64))%2^64 = _
  simp only [Nat.mul_mod,Nat.add_mod,Nat.mod_mod]

#print axioms bitLength
#print axioms value
end R1Z.PV_CBL_ShaBitLength
