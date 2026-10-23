import S9FactoredLoopTwoStepV4
import S9BodyZeroConsumerV1
import S9BodyOneRecordConsumerV1
import S9HighTermSourceCellRootV1
import S9SideOneFrameRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9ActualTwoBodyCompositionV1

open AspisR1S9HelperP6
open AspisR1S9BodyPrefixSemanticsV1

abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical

local instance concreteOps : FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

/-- Both branch witnesses are tied to one successful helper execution and to
its same intermediate array. This is the accepted-run composition boundary;
Rust `from_fn` source correspondence remains separate. -/
structure TwoBodyOutputWitness
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter1 iter2 : R) (initial middle output : W) where
  sideZero : BodyZeroOutputWitness ap0 ap1 extra iter1 initial middle
  sideOne : AspisR1S9BodyOneRecordConsumerV1.BodyOneOutputWitness ap0 ap1 extra iter2 middle output
  output0Canonical : AspisR1.S9SideZeroTailRootV1.canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells output ⟨0, by decide⟩)

theorem successful_helper_has_two_body_witnesses
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (initial output : W)
    (hloop : weights.factored_s2_libra_weights_loop
      AspisR1S9FactoredLoopTwoStepV4.start0 ap0 ap1 extra initial = .ok output)
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    ∃ (iter1 iter2 : R) (middle : W),
      Nonempty (TwoBodyOutputWitness ap0 ap1 extra iter1 iter2 initial middle output) := by
  obtain ⟨iter1, iter2, middle, hnext0, hstart1, hend1,
      hbody0, hnext1, hstart2, hend2, hbody1, hnext2, hdone⟩ :=
    AspisR1S9FactoredLoopTwoStepV4.helper_success_two_body_calls
      ap0 ap1 extra initial output hloop
  have hactive0 : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra 0#usize iter1 initial = .ok (.cont (iter1, middle)) := by
    change AspisR1S9FactoredLoopBodyShapeV3.body ap0 ap1 extra
      (AspisR1S9FactoredLoopTwoStepV4.start0, initial) =
      .ok (.cont (iter1, middle)) at hbody0
    rw [AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
      ap0 ap1 extra AspisR1S9FactoredLoopTwoStepV4.start0 iter1 0#usize initial hnext0] at hbody0
    exact hbody0
  have hside1 : iter1.start = 1#usize := UScalar.eq_of_val_eq hstart1
  have hactive1 : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra 1#usize iter2 middle = .ok (.cont (iter2, output)) := by
    have hraw := hbody1
    change AspisR1S9FactoredLoopBodyShapeV3.body ap0 ap1 extra
      (iter1, middle) = .ok (.cont (iter2, output)) at hraw
    rw [AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
      ap0 ap1 extra iter1 iter2 iter1.start middle hnext1] at hraw
    simpa only [hside1] using hraw
  have hzero := body_zero_output_witness_nonempty
    ap0 ap1 extra iter1 initial middle hactive0 hp0 hp1 hextra
  obtain ⟨zero⟩ := hzero
  have hweights0One : ∀ x, Array.index_usize middle 1#usize = .ok x → Canonical x := by
    intro x hx
    have hcell := AspisR1.S9HighTermPolynomialMeaningRootV1.source_read_cell
      middle 1#usize x (by decide) hx
    rw [← hcell]
    exact zero.output1Canonical
  have hone := AspisR1S9BodyOneRecordConsumerV1.body_one_output_witness_nonempty
    ap0 ap1 extra iter2 middle output hactive1 hp0 hp1 hextra hweights0One
  obtain ⟨one⟩ := hone
  have htailOne := AspisR1S9BodyOneRecordConsumerV1.side_one_source_tail_success
    ap0 ap1 extra iter2 middle output one.prefixData
  have hframe := AspisR1.S9SideOneFrameRootV1.sideOneTail_preserves_cell_zero
    middle ap1 output one.prefixData.low one.prefixData.all one.prefixData.first2
    one.prefixData.q4 one.prefixData.q16 htailOne
  have hframeFin : AspisR1.S9ArrayWriteScheduleRootV1.cells output ⟨0, by decide⟩ =
      AspisR1.S9ArrayWriteScheduleRootV1.cells middle ⟨0, by decide⟩ := by
    change AspisR1.S9ArrayWriteScheduleRootV1.cells output
        (⟨0, by decide⟩ : Fin 4) =
      AspisR1.S9ArrayWriteScheduleRootV1.cells middle
        (⟨0, by decide⟩ : Fin 4)
    exact hframe
  have hout0Canonical : AspisR1.S9SideZeroTailRootV1.canonical
      (AspisR1.S9ArrayWriteScheduleRootV1.cells output ⟨0, by decide⟩) := by
    rw [hframeFin]
    exact zero.output0Canonical
  exact ⟨iter1, iter2, middle, ⟨{ sideZero := zero, sideOne := one, output0Canonical := hout0Canonical }⟩⟩

#print axioms successful_helper_has_two_body_witnesses

end AspisR1S9ActualTwoBodyCompositionV1
