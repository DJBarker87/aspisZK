import R1Z.PV_RunJoin_LayoutConstants64
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FoldedLeafLimits64
open Aeneas Aeneas.Std Result

theorem fibres : Usize.wrapping_shl 1#usize 18#u32=262144#usize := by
  apply UScalar.eq_of_val_eq
  change (Usize.wrapping_shl 1#usize 18#u32).bv.toNat=262144
  rw [Usize.wrapping_shl_bv_eq]
  change ((1#usize).bv <<<(18%System.Platform.numBits)).toNat=262144
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^(18%System.Platform.numBits))%2^System.Platform.numBits=262144
  rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide

theorem populated : Usize.wrapping_shl 1#usize 16#u32=65536#usize := by
  apply UScalar.eq_of_val_eq
  change (Usize.wrapping_shl 1#usize 16#u32).bv.toNat=65536
  rw [Usize.wrapping_shl_bv_eq]
  change ((1#usize).bv <<<(16%System.Platform.numBits)).toNat=65536
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change (1*2^(16%System.Platform.numBits))%2^System.Platform.numBits=65536
  rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide

#print axioms fibres
#print axioms populated
end R1Z.PV_RunJoin_FoldedLeafLimits64
