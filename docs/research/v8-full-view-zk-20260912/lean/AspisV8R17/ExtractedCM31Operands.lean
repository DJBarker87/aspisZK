import AspisV8R17.SourceLazyCM31
import AspisV8R17.CurrentFieldSlice

/-! Focused adapter to the retained CURRENT checked-arithmetic extraction.
Requires its pinned external Aeneas workspace; it is not part of an ordinary
local Mathlib-only replay. No extracted source definition is edited. -/
set_option autoImplicit false
namespace AspisV8R17.ExtractedCM31Operands
open Aeneas Aeneas.Std Result
open V7Tag73CurrentHelpersOpaque

theorem checked_add_success (x y : U64) (h : x.val+y.val<2^64) :
    ∃ z : U64, x+y = ok z ∧ z.val=x.val+y.val := by
  have he := UScalar.add_equiv x y
  cases hr : x+y with
  | ok z => simp only [hr] at he; exact ⟨z, rfl, he.2.1⟩
  | fail err =>
    simp only [hr, UScalar.inBounds, UScalarTy.U64_numBits_eq] at he
    exact False.elim (he h)
  | div => simp only [hr] at he

theorem checked_mul_success (x y : U64) (h : x.val*y.val<2^64) :
    ∃ z : U64, x*y = ok z ∧ z.val=x.val*y.val := by
  have he := UScalar.mul_equiv x y
  change (match (x*y : Result U64) with
    | ok z => x.val*y.val≤UScalar.max .U64 ∧ z.val=x.val*y.val ∧ z.bv=x.bv*y.bv
    | fail _ => UScalar.max .U64<x.val*y.val
    | .div => False) at he
  cases hr : x*y with
  | ok z => simp only [hr] at he; exact ⟨z, rfl, he.2.1⟩
  | fail err =>
    simp only [hr, UScalar.max, UScalarTy.U64_numBits_eq] at he
    omega
  | div => simp only [hr] at he

def crossOperand (a b c d : U32) : Result U64 := do
  let left ← core.convert.num.FromU64U32.from a + core.convert.num.FromU64U32.from b
  let right ← core.convert.num.FromU64U32.from c + core.convert.num.FromU64U32.from d
  left*right

theorem crossOperand_success (a b c d : U32)
    (ha : a.val<RawReducer.P) (hb : b.val<RawReducer.P)
    (hc : c.val<RawReducer.P) (hd : d.val<RawReducer.P) :
    ∃ product : U64, crossOperand a b c d = ok product ∧
      product.val=(a.val+b.val)*(c.val+d.val) := by
  have bounds := lazy_cm31_cross_bounds a.val b.val c.val d.val ha hb hc hd
  have hleft : (core.convert.num.FromU64U32.from a).val+
      (core.convert.num.FromU64U32.from b).val<2^64 := by
    simp only [core.convert.num.FromU64U32.from_val_eq]
    omega
  have hright : (core.convert.num.FromU64U32.from c).val+
      (core.convert.num.FromU64U32.from d).val<2^64 := by
    simp only [core.convert.num.FromU64U32.from_val_eq]
    omega
  obtain ⟨left, hl, hvl⟩ := checked_add_success _ _ hleft
  obtain ⟨right, hr, hvr⟩ := checked_add_success _ _ hright
  simp only [core.convert.num.FromU64U32.from_val_eq] at hvl hvr
  obtain ⟨product, hp, hvp⟩ := checked_mul_success left right (by rw [hvl,hvr]; exact bounds.2.2)
  refine ⟨product, ?_, ?_⟩
  · simp only [crossOperand, hl, hr, bind_tc_ok, hp]
  · simpa only [hvl,hvr] using hvp

theorem current_mul_cross_graph (x y : aspis_core.field.CM31) :
    aspis_core.field.CM31.mul x y = (do
      let m0 ← aspis_core.field.M31.mul x.a y.a
      let m1 ← aspis_core.field.M31.mul x.b y.b
      let product ← crossOperand x.a x.b y.a y.b
      let m2 ← aspis_core.field.M31.reduce_u64 product
      let low ← aspis_core.field.M31.sub m0 m1
      let high0 ← aspis_core.field.M31.sub m2 m0
      let high ← aspis_core.field.M31.sub high0 m1
      ok ⟨low, high⟩) := by
  simp [aspis_core.field.CM31.mul, crossOperand, Std.lift, bind_assoc]

#print axioms checked_add_success
#print axioms checked_mul_success
#print axioms crossOperand_success
#print axioms current_mul_cross_graph
end AspisV8R17.ExtractedCM31Operands
