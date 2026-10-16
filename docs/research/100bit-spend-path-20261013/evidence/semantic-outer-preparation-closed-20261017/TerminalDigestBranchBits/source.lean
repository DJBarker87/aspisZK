import Aeneas.Std
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.BranchBits
open Aeneas Aeneas.Std Result WP
abbrev U64 := UScalar UScalarTy.U64
abbrev Usize := UScalar UScalarTy.Usize

/-- The actual `>>>` then `&&& 1` operations in the frontier loop select the
same zero branch as the retained natural-number model. -/
theorem shifted_low_bit_zero_iff
    (index : U64) (level : Usize) (hlevel : level.val < UScalarTy.U64.numBits)
    (shifted : U64) (hshift : (index >>> level) = .ok shifted)
    (bit : U64) (hbit : lift (shifted &&& (1#u64)) = .ok bit) :
    bit = 0#u64 ↔ ((index.val >>> level.val) &&& 1) = 0 := by
  obtain ⟨shifted', hshift', hshiftSpec⟩ :=
    WP.spec_imp_exists (UScalar.ShiftRight_spec index level hlevel)
  have heq : shifted' = shifted := Result.ok.inj (hshift'.symm.trans hshift)
  subst shifted'
  obtain ⟨bit', hbit', hbitSpec⟩ :=
    WP.spec_imp_exists (UScalar.and_spec shifted (1#u64))
  have hbeq : bit' = bit := Result.ok.inj (hbit'.symm.trans hbit)
  subst bit'
  have hOne : (1#u64).val = 1 := by
    norm_num [UScalar.ofNatCore_val_eq]
  have hbitValue : bit.val = ((index.val >>> level.val) &&& 1) := by
    calc
      bit.val = bit.bv.toNat := rfl
      _ = ((index.bv >>> level.val) &&& (1#u64).bv).toNat := by
        rw [hbitSpec.2, hshiftSpec.2]
      _ = ((index.val >>> level.val) &&& 1) := by
        rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
        simp only [UScalar.bv_toNat, hOne]
  have hzeroVal : (0#u64).val = 0 := by simp [UScalar.ofNatCore_val_eq]
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    rw [hzeroVal, hbitValue] at hv
    exact hv
  · intro h
    apply UScalar.eq_of_val_eq
    rw [hbitValue, hzeroVal]
    exact h

#print axioms shifted_low_bit_zero_iff
end AspisR1TerminalDigestPublicLoop.BranchBits
