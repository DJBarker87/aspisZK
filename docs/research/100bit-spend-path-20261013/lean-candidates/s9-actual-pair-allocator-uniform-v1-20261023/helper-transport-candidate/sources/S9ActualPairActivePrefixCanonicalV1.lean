import S9ActualPairHelperBodyPrefixV1
import S9ActualPairQMOutputCanonicalV1
import S9ActualPairScalarFactorShortV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairActivePrefixCanonicalV1
open AspisR1S9ActualPairHelperBodyPrefixV1
abbrev QC := AspisR1S9ActualPairQMHelperTransportV1.Canonical
abbrev WC := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev GoodArray := AspisR1S9ActualPairScalarCallbackV1.GoodArray
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

/-- All canonicality facts concern values reached in the same accepted actual
active body, including its unused fourth multiplication. The remaining exact
suffix is retained with those same values. -/
theorem actual_active_prefix_canonical (ap0 ap1 : W) (extra : Array Q 2#usize)
    (side : U) (iterNext : R) (weights : W)
    (flow : ControlFlow (R × W) W)
    (hp : GoodArray ap0)
    (hextra : ∀ i q, Array.index_usize extra i = .ok q → QC q)
    (h : pairActiveBody ap0 ap1 extra side iterNext weights = .ok flow) :
    ∃ (q41 q8 q12 q16 : Q) (low : aspis_core.field.wide_exact.WideExact),
      QC q41 ∧ QC q8 ∧ QC q12 ∧ QC q16 ∧ WC low ∧
      pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow := by
  unfold pairActiveBody at h
  obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
  obtain ⟨q1,hq1,h⟩ := bind_success _ _ _ h
  obtain ⟨q2,hq2,h⟩ := bind_success _ _ _ h
  obtain ⟨q3,hq3,h⟩ := bind_success _ _ _ h
  obtain ⟨unused,hunused,h⟩ := bind_success _ _ _ h
  obtain ⟨q4,hq4,h⟩ := bind_success _ _ _ h
  obtain ⟨q41,hq41,h⟩ := bind_success _ _ _ h
  obtain ⟨q8,hq8,h⟩ := bind_success _ _ _ h
  obtain ⟨q12,hq12,h⟩ := bind_success _ _ _ h
  obtain ⟨q16,hq16,h⟩ := bind_success _ _ _ h
  obtain ⟨low,hlow,h⟩ := bind_success _ _ _ h
  have hqc := hextra side q hq
  have hc1 := AspisR1S9PairSourceQMMulCanonicalV1.generated_mul_success_canonical
    _ _ _ AspisR1S9ActualPairQMOutputCanonicalV1.one_canonical hqc hq1
  have hc2 := AspisR1S9PairSourceQMMulCanonicalV1.generated_mul_success_canonical _ _ _ hc1 hqc hq2
  have hc3 := AspisR1S9PairSourceQMMulCanonicalV1.generated_mul_success_canonical _ _ _ hc2 hqc hq3
  have hcu := AspisR1S9PairSourceQMMulCanonicalV1.generated_mul_success_canonical _ _ _ hc3 hqc hunused
  have hi : Array.index_usize (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3]) 2#usize = .ok q2 := by rfl
  have he : q4 = q2 := Result.ok.inj (hq4.symm.trans hi)
  have hc4 : QC q4 := by rw [he]; exact hc2
  have hc41 := AspisR1S9ActualPairQMOutputCanonicalV1.square_success_canonical _ _ hc4 hq41
  have hc8 := AspisR1S9ActualPairQMOutputCanonicalV1.square_success_canonical _ _ hc41 hq8
  have hc12 := AspisR1S9PairSourceQMMulCanonicalV1.generated_mul_success_canonical _ _ _ hc8 hc41 hq12
  have hc16 := AspisR1S9ActualPairQMOutputCanonicalV1.square_success_canonical _ _ hc8 hq16
  have hlowc := (AspisR1S9ActualPairScalarFactorShortV1.actual_scalar_factor_success_maps _ _ _ hp hlow).1
  exact ⟨q41,q8,q12,q16,low,hc41,hc8,hc12,hc16,hlowc,h⟩
#print axioms actual_active_prefix_canonical
end AspisR1S9ActualPairActivePrefixCanonicalV1
