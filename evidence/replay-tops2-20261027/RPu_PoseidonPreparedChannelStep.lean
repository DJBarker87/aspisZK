import RPu_PoseidonPreparedSum3Source
import ExtractedMaskM31AddSub
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelStep

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev U32 := UScalar UScalarTy.U32
abbrev U64 := UScalar UScalarTy.U64
abbrev P : Nat := 2147483647

private def sourceChannelProductAdd (left right : U32) (acc : U64) : Result U64 := do
  let l ← lift (UScalar.cast .U64 left)
  let r ← lift (UScalar.cast .U64 right)
  let product ← l * r
  acc + product

/-- One checked product-and-accumulate step used by the innermost generated
qmsum3 channel loop. Canonical M31 operands and the two-product prefix bound
give a real U64 no-overflow proof for both checked operations. -/
theorem sourceChannelProductAdd_success (left right : U32) (acc : U64)
    (hleft : left.val < P) (hright : right.val < P)
    (hacc : acc.val ≤ 2 * (P - 1) ^ 2) :
    ∃ out : U64,
      sourceChannelProductAdd left right acc = .ok out ∧
      out.val = acc.val + left.val * right.val := by
  have hleft64 : left.val ≤ U64.max := by
    have hb := hleft
    norm_num [P, U64.max, U64.numBits] at hb ⊢
    omega
  have hright64 : right.val ≤ U64.max := by
    have hb := hright
    norm_num [P, U64.max, U64.numBits] at hb ⊢
    omega
  have hleftCastBound : left.val ≤ UScalar.max UScalarTy.U64 := by
    rw [UScalar.max_UScalarTy_U64_eq]
    exact hleft64
  have hrightCastBound : right.val ≤ UScalar.max UScalarTy.U64 := by
    rw [UScalar.max_UScalarTy_U64_eq]
    exact hright64
  have hcastL := UScalar.cast_inBounds_spec .U64 left hleftCastBound
  obtain ⟨l, hcastLrun, hcastLval⟩ := WP.spec_imp_exists hcastL
  have hcastR := UScalar.cast_inBounds_spec .U64 right hrightCastBound
  obtain ⟨r, hcastRrun, hcastRval⟩ := WP.spec_imp_exists hcastR
  have hleftBound : left.val ≤ P - 1 := by omega
  have hrightBound : right.val ≤ P - 1 := by omega
  have hproductBound : left.val * right.val ≤ (P - 1) ^ 2 :=
    Nat.mul_le_mul hleftBound hrightBound
  have htotalBound : acc.val + left.val * right.val ≤ 3 * (P - 1) ^ 2 := by
    omega
  have hwordBound : 3 * (P - 1) ^ 2 ≤ U64.max := by
    norm_num [P, U64.max, U64.numBits]
  have hmulBound : l.val * r.val ≤ U64.max := by
    rw [hcastLval, hcastRval]
    exact le_trans hproductBound (by omega)
  have hmul : (l * r : Result U64) ⦃z => z.val = l.val * r.val⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_UScalarTy_U64_eq] using hmulBound
  obtain ⟨product, hmulRun, hmulVal⟩ := WP.spec_imp_exists hmul
  have haddBound : acc.val + product.val ≤ U64.max := by
    rw [hmulVal, hcastLval, hcastRval]
    exact le_trans htotalBound hwordBound
  have hadd : (acc + product : Result U64) ⦃z => z.val = acc.val + product.val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_UScalarTy_U64_eq] using haddBound
  obtain ⟨out, haddRun, haddVal⟩ := WP.spec_imp_exists hadd
  refine ⟨out, ?_, ?_⟩
  · simp [sourceChannelProductAdd, hcastLrun, hcastRrun, hmulRun, haddRun]
  · rw [haddVal, hmulVal, hcastLval, hcastRval]

#print axioms sourceChannelProductAdd_success
end AspisR1PoseidonPreparedChannelStep
