import S9CandidateTopTransportDischargerV1
import S9SelectedOutputCanonicalV1
import S9CandidateOriginalCoefficientsBridgeV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateOutputCanonicalV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1
open AspisR1S9CandidateTopTransportDischargerV1
open AspisR1S9SelectedOutputCanonicalV1

abbrev U := Std.Usize
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PArray := Array PW (4#usize)
abbrev Canonical := AspisR1S9SelectedOutputCanonicalV1.Canonical

private theorem generated_to_current_q (x : AspisR1S9HelperP6.field.QM31) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

private theorem generated_to_current_w (x : PW) :
    AspisR1S9GeneratedWideMulQM31V2.toWide x =
      AspisR1S9CurrentFieldOpsV1.toE x := by
  cases x <;> rfl

/-- The same successful candidate top call transported to the selected P6
helper has four canonical returned cells. All canonical-read premises are the
ones used by the top suffix discharger and the selected helper theorem. -/
theorem candidate_top_success_output_all_canonical
    (ap0 ap1 : Array CW (4#usize)) (extra : Array CQ (2#usize))
    (output : Array CW (4#usize))
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
    ∀ j : Fin 4,
      Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells
        (mapArray AspisR1S9CandidateHelperV1.toP6W output) j) := by
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
  have hp1Selected : ∀ (j : U) (x : PW),
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
  have hextraSelected : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x := by
    intro j x hx
    obtain ⟨xc, hxc, hmap⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv AspisR1S9CandidateHelperV1.toP6Q extra j x hx
    have hc := hextra j xc hxc
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM
        (AspisR1S9CandidateHelperV1.toP6Q xc)) at hc
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)
    rw [← hmap, ← generated_to_current_q]
    exact hc
  exact AspisR1S9SelectedOutputCanonicalV1.successful_selected_helper_output_all_canonical
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
    (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) initial
    (mapArray AspisR1S9CandidateHelperV1.toP6W output)
    hloopP6 hp0 hp1Selected hextraSelected

#print axioms candidate_top_success_output_all_canonical

end AspisR1S9CandidateOutputCanonicalV1
