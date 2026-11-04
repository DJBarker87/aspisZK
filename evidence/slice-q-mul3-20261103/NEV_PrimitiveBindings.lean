import NEV_AccumulateCallees
import NEV_StageWideFields
set_option autoImplicit false
noncomputable section
namespace NEV_PrimitiveBindings
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

theorem power (x y : RawQ) (hx : NBF_PowerStep.Canonical (toQ x))
    (hy : NBF_PowerStep.Canonical (toQ y)) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.QM31.mul x y;ok (toQ out)) =
      NBO_FieldSemantics.power (toQ x) (toQ y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.QM31.mul
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NEV_StageFields.power (toQ x) (toQ y) hx hy

theorem add (x y : RawE) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hy : NBO_TailDomain.WideCanonical (toE y)) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add x y;ok (toE out)) =
      NBO_FieldSemantics.add (toE x) (toE y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NEV_StageWideFields.add (toE x) (toE y) hx hy

theorem product (x : RawE) (q : RawQ) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hq : NBF_PowerStep.Canonical (toQ q)) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q;ok (toE out)) =
      NBO_FieldSemantics.product (toE x) (toQ q) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NEV_StageWideFields.product (toE x) (toQ q) hx hq

/-- The exact field call itself supplies the next call's canonical domain.
A returned product or its successful result is never a premise. -/
theorem product_returns (x : RawE) (q : RawQ) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hq : NBF_PowerStep.Canonical (toQ q)) :
    ∃ out,NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q=ok out ∧
      NBO_TailDomain.WideCanonical (toE out) := by
  obtain ⟨model,run,canonical⟩ := NBO_FieldSemantics.product_total (toE x) (toQ q) hx hq
  have same := (product x q hx hq).trans run
  cases actual : NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q with
  | fail error => simp only [actual,bind_tc_fail] at same;contradiction
  | div => simp only [actual,bind_tc_div] at same;contradiction
  | ok out =>
    simp only [actual,bind_tc_ok] at same
    have equality := Result.ok.inj same
    refine ⟨out,rfl,?_⟩
    rw [equality]
    exact canonical
#print axioms power
#print axioms add
#print axioms product
#print axioms product_returns
end NEV_PrimitiveBindings
end
