import S5PairCutRangeLoopTraceV1
import FourDotsPushProductTraceRootV1
import S4TailFieldProductRootV1
import EbyKPushPairFinishDecodedV1
import EbyKPushPairInitializedV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5PairCutRangeDecodedProductV3

open AspisR1S5PairCutRangeLoopTraceV1
open AspisR1S5PairCutLoopFoldV1
open AspisR1S5PairCutFieldCallbackV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsWrapperLawsV1
open AspisR1S5EbyKPushPairInitializedV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=
  sourceOps

abbrev PairDot := AspisR1S5PairCutRangeLoopTraceV1.PairDot
abbrev Range := AspisR1S5PairCutRangeLoopTraceV1.Range
abbrev Output := AspisR1S5PairCutRangeLoopTraceV1.Output
abbrev CutWide := AspisR1WeightsPairCut.field.WideExact
abbrev CutQM := AspisR1WeightsPairCut.field.QM31
abbrev PushState := AspisR1EbyKPushDotBackend.PushState
abbrev PushWide := AspisR1EbyKPushDotBackend.PushWide
abbrev PushQM := AspisR1EbyKPushDotBackend.PushQm

private theorem range_trace_pushes_to_source
    (read : Slice U8 → Usize → Result CutWide)
    (bytes : Slice U8) (scratch : Slice CutQM) (n : Usize)
    (iter : Range) (pair out : PairDot) (js : List Usize)
    (hvalid : ∀ j value scalar, read bytes j = .ok value →
      Slice.index_usize scratch j = .ok scalar →
      AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
        (wideToSource value))
    (htrace : CallbackRangeTrace read bytes scratch n iter pair js out) :
    ∃ xs : List (PushWide × PushQM),
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        (stateToSource pair) xs (stateToSource out) ∧
      (∀ p ∈ xs, AspisR1EbyKPowerValueCanonicalToPush.pushCanonical p.1) ∧
      List.Forall₂ (fun j p => ∃ value scalar,
        read bytes j = .ok value ∧
        Slice.index_usize scratch j = .ok scalar ∧
        p = (wideToSource value, qToSource scalar)) js xs := by
  induction htrace with
  | done iter pair hend hat hout =>
      cases hout
      refine ⟨[], AspisR1DotCountBoundV1.AcceptedPushTrace.nil _, ?_, ?_⟩
      · simp
      · exact List.Forall₂.nil
  | @step iter iter' pair pair' out j js value scalar hend hnext hread hscalar hpush htail ih =>
      obtain ⟨xs, htailTrace, htailCanonical, htailCorrespondence⟩ := ih
      obtain ⟨sourceMid, hsource, hmap⟩ :=
        installed_push_success_map pair value scalar (.Ok ()) pair' hpush
      have hsource' : AspisR1EbyKPushDotBackend.pushWithDotBackend
          AspisR1EbyKPushDecodedProductUpdate.QRaw (stateToSource pair)
          (wideToSource value) (qToSource scalar) = .ok (.Ok (), sourceMid) := by
        simpa [sourceOps] using hsource
      have hmid : sourceMid = stateToSource pair' := by
        have h := congrArg stateToSource hmap
        simpa [stateToFrom] using h
      rw [← hmid] at htailTrace
      have hcanonical := hvalid j value scalar hread hscalar
      refine ⟨(wideToSource value, qToSource scalar) :: xs,
        AspisR1DotCountBoundV1.AcceptedPushTrace.cons _ _ _ _ _ _ hsource' htailTrace,
        ?_, List.Forall₂.cons ⟨value, scalar, hread, hscalar, rfl⟩ htailCorrespondence⟩
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · cases hp
        exact hcanonical
      · exact htailCanonical p hp

/-- A successful source-shaped range loop has the exact decoded product sum
of the same returned PairDot. The field reader remains a callback boundary,
but its canonical-output property is quantified over every successful read.
This theorem does not claim forward totality of the range loop. -/
theorem successful_run_decoded_product_sum
    (read : Slice U8 → Usize → Result CutWide)
    (bytes : Slice U8) (scratch : Slice CutQM)
    (n : Usize) (iter : Range) (pair out : PairDot)
    (hend : iter.end.val = n.val)
    (hstart : iter.start.val ≤ n.val)
    (hrun : run read bytes scratch iter pair = .ok (.Ok (), out))
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c1.sums)
    (hvalid : ∀ j value scalar, read bytes j = .ok value →
      Slice.index_usize scratch j = .ok scalar →
      AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
        (wideToSource value)) :
    ∃ indices xs currentOut,
      CallbackRangeTrace read bytes scratch n iter pair indices out ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        (stateToSource pair) xs (stateToSource out) ∧
      List.Forall₂ (fun j p => ∃ value scalar,
        read bytes j = .ok value ∧
        Slice.index_usize scratch j = .ok scalar ∧
        p = (wideToSource value, qToSource scalar)) indices xs ∧
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish out =
        .ok (wideFromSource currentOut) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
        AspisR1FastDotsTailFieldProductRootV1.decodeState
          (stateValue (stateToSource pair)) + productSum xs := by
  obtain ⟨indices, htrace, _hlen⟩ :=
    successful_run_has_trace read bytes scratch n iter pair out hend hstart hrun
  obtain ⟨xs, haccepted, hcanonical, hreadMap⟩ :=
    range_trace_pushes_to_source read bytes scratch n iter pair out indices hvalid htrace
  have hproduct := accepted_trace_product_sum
    (stateToSource pair) (stateToSource out) xs hinv0 hinv1 hcanonical haccepted
  have hdecodeProduct := decode_product_fold xs
    (stateValue (stateToSource pair))
  rw [← hproduct] at hdecodeProduct
  obtain ⟨currentOut, hfinish, hfinishDecode⟩ :=
    AspisR1S5EbyKPushPairFinishDecodedV1.installed_finish_decoded_state out
  refine ⟨indices, xs, currentOut, htrace, haccepted, hreadMap, hfinish, ?_⟩
  calc
    AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
        decodeState (stateValue (stateToSource out)) := hfinishDecode
    _ = AspisR1FastDotsTailFieldProductRootV1.decodeState
        (stateValue (stateToSource pair)) + productSum xs := hdecodeProduct

/-- The retained checked field callback discharges the per-success canonical
output condition from its own parser theorem. The emitted PairCut reader still
needs a separate source/extraction equality to instantiate this result. -/
theorem checked_field_run_decoded_product_sum
    (bytes : Slice U8) (scratch : Slice CutQM)
    (n : Usize) (iter : Range) (pair out : PairDot)
    (hend : iter.end.val = n.val)
    (hstart : iter.start.val ≤ n.val)
    (hrun : run checkedFieldCallback bytes scratch iter pair = .ok (.Ok (), out))
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c1.sums) :
    ∃ indices xs currentOut,
      CallbackRangeTrace checkedFieldCallback bytes scratch n iter pair indices out ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        (stateToSource pair) xs (stateToSource out) ∧
      List.Forall₂ (fun j p => ∃ value scalar,
        checkedFieldCallback bytes j = .ok value ∧
        Slice.index_usize scratch j = .ok scalar ∧
        p = (wideToSource value, qToSource scalar)) indices xs ∧
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish out =
        .ok (wideFromSource currentOut) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
        AspisR1FastDotsTailFieldProductRootV1.decodeState
          (stateValue (stateToSource pair)) + productSum xs := by
  apply successful_run_decoded_product_sum checkedFieldCallback bytes scratch n
    iter pair out hend hstart hrun hinv0 hinv1
  intro j value scalar hread _hscalar
  exact checkedFieldCallback_success_push_canonical bytes j value hread

#print axioms successful_run_decoded_product_sum
#print axioms checked_field_run_decoded_product_sum
end AspisR1S5PairCutRangeDecodedProductV3
