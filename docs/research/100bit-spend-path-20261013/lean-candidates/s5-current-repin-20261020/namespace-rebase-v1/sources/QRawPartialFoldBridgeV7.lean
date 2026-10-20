import Aeneas
import AspisR1CanonicalQRawUnified.Funs
import AspisV8R17.RawReducerNat
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1CanonicalQRawUnified.Proof
open AspisV8R17.RawReducer

abbrev U32 := UScalar UScalarTy.U32
abbrev U64 := UScalar UScalarTy.U64

def qRawMask64 : U64 := core.convert.num.FromU64U32.from canonical.P

theorem qRawMask64_val : qRawMask64.val = P := by
  have hp : canonical.P.val = P := by
    norm_num [canonical.P, P, UScalar.ofNatCore_val_eq]
  have hcast : qRawMask64.val = canonical.P.val := by
    change (UScalar.cast .U64 canonical.P).val = canonical.P.val
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by
      rw [hp]
      norm_num)
  exact hcast.trans hp

theorem qRawPartial_success (x : U64) :
    ∃ out : U64,
      canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
        .ok out ∧ out.val = foldBits x.val := by
  obtain ⟨masked, hmasked, hmaskedVal⟩ :=
    WP.spec_imp_exists (UScalar.and_spec x qRawMask64)
  have hshiftBound : (31#i32).val < UScalarTy.U64.numBits := by
    norm_num [UScalar.ofNatCore_val_eq]
  have hshiftNonneg : 0 ≤ (31#i32).val := by norm_num
  obtain ⟨shifted, hshifted, hshiftedVal⟩ :=
    WP.spec_imp_exists (UScalar.ShiftRight_IScalar_spec x (31#i32) hshiftNonneg hshiftBound)
  have h31 : (31#i32).val = 31 := by
    norm_num [UScalar.ofNatCore_val_eq]
  have hshiftNat : (31#i32).toNat = 31 := by rfl
  have hsum : masked.val + shifted.val = foldBits x.val := by
    rw [hmaskedVal.1, hshiftedVal.1, hshiftNat, UScalar.val_and, qRawMask64_val]
    rfl
  have hx : x.val < 2 ^ UScalarTy.U64.numBits := x.bv.isLt
  have hwidth : UScalarTy.U64.numBits = 64 := by rfl
  rw [hwidth] at hx
  have hfoldBound : foldBits x.val < 2 ^ 64 := by
    calc
      foldBits x.val < 10737418240 := first_fold_lt x.val hx
      _ < 2 ^ 64 := by norm_num
  have hvalue : (UScalar.wrapping_add masked shifted).val = foldBits x.val := by
    rw [UScalar.wrapping_add_val_eq]
    simp only [UScalar.size, UScalarTy.U64_numBits_eq]
    rw [hsum, Nat.mod_eq_of_lt hfoldBound]
  have hcall :
      canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
        .ok (UScalar.wrapping_add masked shifted) := by
    unfold canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
    have hcast : lift (core.convert.num.FromU64U32.from canonical.P) = .ok qRawMask64 := rfl
    rw [hcast]
    simp only [Aeneas.Std.bind_tc_ok, hmasked, hshifted]
    rfl
  exact ⟨_, hcall, hvalue⟩

#print axioms qRawMask64_val
#print axioms qRawPartial_success
end AspisR1CanonicalQRawUnified.Proof
