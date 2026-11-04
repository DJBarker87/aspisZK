import NEV_PrimitiveBindings
set_option autoImplicit false
noncomputable section
namespace NEV_PrimitiveTotal
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

theorem add (x y : RawE) (hx : NBO_TailDomain.WideCanonical (toE x))
    (hy : NBO_TailDomain.WideCanonical (toE y)) :
    ∃ out,NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add x y=ok out ∧
      NBO_TailDomain.WideCanonical (toE out) := by
  obtain ⟨model,run,canonical⟩ := NBO_FieldSemantics.add_total (toE x) (toE y) hx hy
  obtain ⟨out,actual,value⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _
    ((NEV_PrimitiveBindings.add x y hx hy).trans run)
  refine ⟨out,actual,?_⟩
  rw [Result.ok.inj value]
  exact canonical

theorem power (x y : RawQ) (hx : NBF_PowerStep.Canonical (toQ x))
    (hy : NBF_PowerStep.Canonical (toQ y)) :
    ∃ out,NEV_AccumulateRaw.aspis_core.field.QM31.mul x y=ok out ∧
      NBF_PowerStep.Canonical (toQ out) := by
  obtain ⟨model,run,canonical⟩ := NBO_FieldSemantics.power_total (toQ x) (toQ y) hx hy
  obtain ⟨out,actual,value⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _
    ((NEV_PrimitiveBindings.power x y hx hy).trans run)
  refine ⟨out,actual,?_⟩
  rw [Result.ok.inj value]
  exact canonical
#print axioms add
#print axioms power
end NEV_PrimitiveTotal
end
