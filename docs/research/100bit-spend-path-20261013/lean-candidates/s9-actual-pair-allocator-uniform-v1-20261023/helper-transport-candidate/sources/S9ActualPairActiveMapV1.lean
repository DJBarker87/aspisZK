import S9ActualPairAfterLowMapV1
import S9ActualPairAfterLowCanonicalV1
import S9ActualPairHelperBodyPrefixV1
import S9ActualPairQMOutputCanonicalV1
import S9ActualPairScalarFactorShortV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairActiveMapV1
open AspisR1S9ActualPairHelperBodyPrefixV1
open AspisR1S9ActualPairOldCarrierScalarV1
open AspisR1S9ActualPairOldPrimitiveSuccessV1
abbrev Q := aspis_core.field.QM31
abbrev W := AspisR1S9ActualPairHelperBodyPrefixV1.W
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
theorem actual_active_success_maps (ap0 ap1 : W) (extra : Array Q 2#usize)
    (side : U) (iterNext : R) (weights : W)
    (flow : ControlFlow (R × W) W)
    (hp : GoodArray ap0) (hp1 : GoodArray ap1) (hw : GoodArray weights)
    (hextra : ∀ i q, Array.index_usize extra i = .ok q → QC q)
    (h : pairActiveBody ap0 ap1 extra side iterNext weights = .ok flow) :
    ∃ output, flow = .cont (iterNext,output) ∧ GoodArray output ∧
      AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra)
        side iterNext (mapArray toOldW weights) =
        .ok (.cont (iterNext,mapArray toOldW output)) := by
  unfold pairActiveBody at h
  obtain ⟨q,hq,hstep1⟩ := bind_success _ _ _ h
  obtain ⟨q1,hq1,hstep2⟩ := bind_success _ _ _ hstep1
  obtain ⟨q2,hq2,hstep3⟩ := bind_success _ _ _ hstep2
  obtain ⟨q3,hq3,hstep4⟩ := bind_success _ _ _ hstep3
  obtain ⟨unused,hunused,hstep5⟩ := bind_success _ _ _ hstep4
  obtain ⟨q4,hq4,hstep6⟩ := bind_success _ _ _ hstep5
  obtain ⟨q41,hq41,hstep7⟩ := bind_success _ _ _ hstep6
  obtain ⟨q8,hq8,hstep8⟩ := bind_success _ _ _ hstep7
  obtain ⟨q12,hq12,hstep9⟩ := bind_success _ _ _ hstep8
  obtain ⟨q16,hq16,hstep10⟩ := bind_success _ _ _ hstep9
  obtain ⟨low,hlow,hstep11⟩ := bind_success _ _ _ hstep10
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
  obtain ⟨output,hflow,hmodel⟩ := AspisR1S9ActualPairAfterLowMapV1.actual_after_low_success_maps
    ap1 side iterNext weights q41 q8 q12 q16 low flow hc41 hc16 hp1 hw hlowc hstep11
  obtain ⟨canout,hcanflow,hcan⟩ := AspisR1S9ActualPairAfterLowCanonicalV1.actual_after_low_preserves
    ap1 side iterNext weights q41 q8 q12 q16 low flow hp1 hw hlowc hstep11
  have hpair : (iterNext,output) = (iterNext,canout) :=
    ControlFlow.cont.inj (hflow.symm.trans hcanflow)
  have heout : output = canout := congrArg Prod.snd hpair
  have houtput : GoodArray output := by rw [heout]; exact hcan
  have mq := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result toOldQ extra side
  rw [hq] at mq
  change .ok (toOldQ q) = Array.index_usize (mapArray toOldQ extra) side at mq
  have mq1 := qm_mul_success _ _ _ AspisR1S9ActualPairQMOutputCanonicalV1.one_canonical hqc hq1
  rw [one_maps] at mq1
  have mq2 := qm_mul_success _ _ _ hc1 hqc hq2
  have mq3 := qm_mul_success _ _ _ hc2 hqc hq3
  have mqu := qm_mul_success _ _ _ hc3 hqc hunused
  have hmake : mapArray toOldQ (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3]) =
      Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,toOldQ q1,toOldQ q2,toOldQ q3] := by
    have hh : mapArray toOldQ (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3]) =
        Array.make 4#usize [toOldQ aspis_core.field.QM31.ONE,toOldQ q1,toOldQ q2,toOldQ q3] := by rfl
    rw [one_maps] at hh
    exact hh
  have mq4 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result toOldQ
    (Array.make 4#usize [aspis_core.field.QM31.ONE,q1,q2,q3]) 2#usize
  rw [hq4] at mq4
  have hindex := congrArg (fun (a : Array OQ 4#usize) => Array.index_usize a 2#usize) hmake
  have mq4Target : Array.index_usize
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,toOldQ q1,toOldQ q2,toOldQ q3])
      2#usize = .ok (toOldQ q4) := hindex.symm.trans mq4.symm
  have mq41 := qm_square_success _ _ hc4 hq41
  have mq8 := qm_square_success _ _ hc41 hq8
  have mq12 := qm_mul_success _ _ _ hc8 hc41 hq12
  have mq16 := qm_square_success _ _ hc8 hq16
  have mlowRaw := actual_scalar_success_to_old _ _ _ hp hlow
  have hscalar := congrArg (fun (ff : Array OQ 4#usize) =>
    AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor ff (mapArray toOldW ap0)) hmake
  have mlow : AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,toOldQ q1,toOldQ q2,toOldQ q3])
      (mapArray toOldW ap0) = .ok (toOldW low) := hscalar.symm.trans mlowRaw
  refine ⟨output,hflow,houtput,?_⟩
  unfold AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
  simp only [←mq,mq1,mq2,mq3,mqu,mq4Target,mq41,mq8,mq12,mq16,mlow,bind_tc_ok]
  exact hmodel
#print axioms actual_active_success_maps
end AspisR1S9ActualPairActiveMapV1
