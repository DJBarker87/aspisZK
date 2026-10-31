import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LayoutConstants64
open Aeneas Aeneas.Std Result ProverRwFull

theorem fibres : aspis_core.r0.FIBRE_COUNT=ok 262144#usize := by
  unfold aspis_core.r0.FIBRE_COUNT
  change (if (18 : Int)≥0 then UScalar.shiftLeft 1#usize 18 else Result.fail Error.integerOverflow)=ok 262144#usize
  rw [if_pos (by decide)]
  unfold UScalar.shiftLeft
  rw [if_pos (by have h := System.Platform.numBits_eq;change 18<System.Platform.numBits;omega)]
  congr 1
  apply UScalar.eq_of_val_eq
  change ((1#usize).bv <<<18).toNat=262144
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^18)%2^System.Platform.numBits=262144
  rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide

theorem words : aspis_core.r0.WORD_LEN=ok 1048576#usize := by
  unfold aspis_core.r0.WORD_LEN
  change (if (20 : Int)≥0 then UScalar.shiftLeft 1#usize 20 else Result.fail Error.integerOverflow)=ok 1048576#usize
  rw [if_pos (by decide)]
  unfold UScalar.shiftLeft
  rw [if_pos (by have h := System.Platform.numBits_eq;change 20<System.Platform.numBits;omega)]
  congr 1
  apply UScalar.eq_of_val_eq
  change ((1#usize).bv <<<20).toNat=1048576
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^20)%2^System.Platform.numBits=1048576
  rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide

#print axioms fibres
#print axioms words
end R1Z.PV_RunJoin_LayoutConstants64
