import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LayoutConstants64
open Aeneas Aeneas.Std Result ProverRwFull

theorem fibres : aspis_core.r0.FIBRE_COUNT=ok 262144#usize := by
  unfold aspis_core.r0.FIBRE_COUNT
  change ok (Usize.wrapping_shl 1#usize 18#u32)=ok 262144#usize
  congr 1
  apply UScalar.eq_of_val_eq
  change (Usize.wrapping_shl 1#usize 18#u32).bv.toNat=262144
  rw [Usize.wrapping_shl_bv_eq,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^(18%System.Platform.numBits))%2^System.Platform.numBits=262144
  rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide

theorem words : aspis_core.r0.WORD_LEN=ok 1048576#usize := by
  unfold aspis_core.r0.WORD_LEN
  change ok (Usize.wrapping_shl 1#usize 20#u32)=ok 1048576#usize
  congr 1
  apply UScalar.eq_of_val_eq
  change (Usize.wrapping_shl 1#usize 20#u32).bv.toNat=1048576
  rw [Usize.wrapping_shl_bv_eq,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^(20%System.Platform.numBits))%2^System.Platform.numBits=1048576
  rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide

#print axioms fibres
#print axioms words
end R1Z.PV_RunJoin_LayoutConstants64
