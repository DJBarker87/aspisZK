import S9ConstructorV3FactorsCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3VariantPreservedV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3
/-- The actual extracted V3 constructor stores its own input variant on
accepted runs. No canonical-input, allocation-content or output contract is
assumed. Source/runtime normalization remains a separate boundary. -/
theorem constructor_success_variant_preserved
    (variant : Variant) (alpha : Array field.QM31 10#usize)
    (z : Array circle.SecureCirclePoint 2#usize) (w : Weights)
    (hnew : weights_new variant alpha z = .ok (.Ok w)) : w.variant = variant := by
  unfold weights_new at hnew
  obtain ⟨points, hpoints, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨q8, hq8, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨q9, hq9, hnew⟩ := bind_success_inv _ _ _ hnew
  change (do
    let factors1 ← weights_new_loop0 {start := 0#usize, «end» := 3#usize} points
      AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initialFactors
    let factors2 ← weights_new_loop1 {start := 0#usize, «end» := 2#usize} z factors1
    let result ← Weights.box_from_parts variant factors2 points (Array.make 2#usize [q8,q9])
    ok (core.result.Result.Ok result)) = .ok (core.result.Result.Ok w) at hnew
  obtain ⟨factors1, hphase1, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨factors2, hphase2, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨boxed, hbox, hnew⟩ := bind_success_inv _ _ _ hnew
  have hboxed : boxed = w := core.result.Result.Ok.inj (Result.ok.inj hnew)
  subst boxed
  change Result.ok (Weights.mk variant factors2 points (Array.make 2#usize [q8,q9])) = Result.ok w at hbox
  have hw : Weights.mk variant factors2 points (Array.make 2#usize [q8,q9]) = w := Result.ok.inj hbox
  rw [← hw]

#print axioms constructor_success_variant_preserved
end AspisR1S9ConstructorV3VariantPreservedV1
