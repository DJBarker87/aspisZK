import S5PairCutRangeDecodedProductV3
import S5PairCutTransparentReaderAdapterV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5PairCutActualReaderProductV1

open AspisR1S5PairCutRangeDecodedProductV3
open AspisR1S5PairCutLoopFoldV1
open AspisR1S5PairCutTransparentReaderV1
open AspisR1S5PairCutFieldCallbackV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsWrapperLawsV1
open AspisR1S5EbyKPushPairInitializedV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=
  sourceOps

/-- A successful selected PairCut candidate range run whose read operation is
instantiated with the emitted selector skeleton and actual strict decoder has
the same indexed product meaning as the checked-reader theorem. The checked
callback equality and canonicality are discharged here, rather than supplied
as a reader hypothesis. This remains the normalized extracted-candidate
operational model; the source/Std loop linkage is separate. -/
theorem emitted_reader_run_decoded_product_sum
    (bytes : Slice U8) (scratch : Slice CutQM)
    (n : Usize) (iter : Range) (pair out : PairDot)
    (hend : iter.end.val = n.val)
    (hstart : iter.start.val ≤ n.val)
    (hrun : AspisR1S5PairCutRangeLoopTraceV1.run (readerBody actualPairDecoder) bytes scratch iter pair =
      .ok (.Ok (), out))
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c1.sums) :
    ∃ indices xs currentOut,
      AspisR1S5PairCutRangeLoopTraceV1.CallbackRangeTrace (readerBody actualPairDecoder) bytes scratch n iter pair indices out ∧
      AspisR1DotCountBoundV1.AcceptedPushTrace
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        (stateToSource pair) xs (stateToSource out) ∧
      List.Forall₂ (fun j p => ∃ value scalar,
        (readerBody actualPairDecoder) bytes j = .ok value ∧
        Slice.index_usize scratch j = .ok scalar ∧
        p = (wideToSource value, qToSource scalar)) indices xs ∧
      AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish out =
        .ok (wideFromSource currentOut) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
        AspisR1FastDotsTailFieldProductRootV1.decodeState
          (stateValue (stateToSource pair)) + productSum xs := by
  apply successful_run_decoded_product_sum
    (readerBody actualPairDecoder) bytes scratch n iter pair out
    hend hstart hrun hinv0 hinv1
  intro j value scalar hread _hscalar
  rw [actualReader_eq_checkedCallback] at hread
  exact checkedFieldCallback_success_push_canonical bytes j value hread

#print axioms emitted_reader_run_decoded_product_sum
end AspisR1S5PairCutActualReaderProductV1
