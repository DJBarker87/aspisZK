import S9CandidateTopTransportDischargerV1
import S9SelectedHelperOriginalCoefficientsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateOriginalCoefficientsBridgeV4

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1
open AspisR1S9CandidateTopTransportDischargerV1
open AspisR1S9SelectedHelperOriginalCoefficientsV10

abbrev U := Std.Usize
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PArray := Array PW (4#usize)
abbrev TraceDecode := AspisR1S9SelectedHelperOriginalCoefficientsV10.TraceDecode
abbrev ScaledBase := AspisR1S9SelectedHelperOriginalCoefficientsV10.ScaledBase
abbrev Seed := AspisR1S9SelectedHelperOriginalCoefficientsV10.Seed

private theorem generated_to_current_q (x : AspisR1S9HelperP6.field.QM31) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

private theorem generated_to_current_w (x : PW) :
    AspisR1S9GeneratedWideMulQM31V2.toWide x =
      AspisR1S9CurrentFieldOpsV1.toE x := by
  cases x <;> rfl

theorem mapped_read_inv {A B : Type} {N : Usize}
    (f : A → B) (a : Array A N) (i : Usize) (y : B)
    (h : Array.index_usize (mapArray f a) i = .ok y) :
    ∃ x, Array.index_usize a i = .ok x ∧ f x = y := by
  have hm := mapArray_index_result f a i
  rw [← hm] at h
  cases hx : Array.index_usize a i with
  | fail e => simp [hx, mapResult] at h
  | div => simp [hx, mapResult] at h
  | ok x =>
      simp [hx, mapResult] at h
      exact ⟨x, rfl, h⟩

/-- A successful generated candidate wrapper call yields the original four
coefficient equations for the mapped output array. The top transport discharger
constructs the suffix correspondence from the exact successful candidate
suffix executions; `hp0` remains explicit for the selected P6 model. No frozen
Rust/Std correspondence is asserted here. -/
theorem candidate_top_success_has_original_coefficients
    (ap0 ap1 : Array CW (4#usize)) (extra : Array CQ (2#usize)) (output : Array CW (4#usize))
    (htop : AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output)
    (hp0 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap0) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x)) :
    ∃ q0 q1 : CQ,
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      ∀ j : Fin 4,
        TraceDecode (AspisR1.S9ArrayWriteScheduleRootV1.cells
          (mapArray AspisR1S9CandidateHelperV1.toP6W output) j) =
        AspisR1.S2LibraFactoredIdentity.original
          (ScaledBase (mapArray AspisR1S9CandidateHelperV1.toP6W ap0))
          (ScaledBase (mapArray AspisR1S9CandidateHelperV1.toP6W ap1))
          (Seed (AspisR1S9CandidateHelperV1.toP6Q q0))
          (Seed (AspisR1S9CandidateHelperV1.toP6Q q1)) j := by
  have htopP6 := AspisR1S9CandidateTopTransportDischargerV1.candidate_top_success_maps_to_p6
    ap0 ap1 extra output htop hextra hap1
  let initial : PArray := Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO
  have hloopP6 : @AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      AspisR1S9FactoredLoopTwoStepV4.start0
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) initial =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output) := by
    unfold _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights at htopP6
    change @AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      AspisR1S9FactoredLoopTwoStepV4.start0
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) initial =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output) at htopP6
    exact htopP6
  have hp1Original : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x := by
    intro j x hx
    have hc := hap1 j x hx
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x) at hc
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE x)
    rw [← generated_to_current_w x]
    exact hc
  have hextraOriginal : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x := by
    intro j x hx
    obtain ⟨xc, hxc, hmap⟩ := mapped_read_inv AspisR1S9CandidateHelperV1.toP6Q extra j x hx
    have hc := hextra j xc hxc
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM
        (AspisR1S9CandidateHelperV1.toP6Q xc)) at hc
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)
    rw [← hmap, ← generated_to_current_q]
    exact hc
  obtain ⟨q0p, q1p, hq0p, hq1p, hcoeff⟩ :=
    AspisR1S9SelectedHelperOriginalCoefficientsV10.successful_selected_helper_has_original_coefficients
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) initial
      (mapArray AspisR1S9CandidateHelperV1.toP6W output)
      hloopP6 hp0 hp1Original hextraOriginal
  obtain ⟨q0c, hq0c, hq0map⟩ :=
    mapped_read_inv AspisR1S9CandidateHelperV1.toP6Q extra 0#usize q0p hq0p
  obtain ⟨q1c, hq1c, hq1map⟩ :=
    mapped_read_inv AspisR1S9CandidateHelperV1.toP6Q extra 1#usize q1p hq1p
  refine ⟨q0c, q1c, hq0c, hq1c, ?_⟩
  intro j
  have hj := hcoeff j
  rw [← hq0map, ← hq1map] at hj
  exact hj

#print axioms mapped_read_inv
#print axioms candidate_top_success_has_original_coefficients

end AspisR1S9CandidateOriginalCoefficientsBridgeV4
