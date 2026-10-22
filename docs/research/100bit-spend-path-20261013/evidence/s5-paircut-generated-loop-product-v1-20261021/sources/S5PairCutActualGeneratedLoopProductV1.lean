import S5PairCutActualReaderProductV1
import S5PairCutActualGeneratedBodyV15
import AspisR1WeightsPairCut.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5PairCutActualGeneratedLoopProductV1

open AspisR1S5PairCutActualReaderProductV1
open AspisR1S5PairCutRangeDecodedProductV3
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1S5PairCutTransparentReaderV1
open AspisR1S5PairCutRangeLoopTraceV1
open AspisR1WeightsPairCutEbyKDotOpsV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=
  AspisR1S5EbyKConcreteOpsInstanceV1.sourceOps

/-- A successful emitted PairCut loop, with the exact generated body and the
selected strict decoder installed, inherits the indexed product/read trace
meaning of the selected range-loop theorem. This composes the source-shaped
body equality with the reader specialization; it does not assert the separate
Rust Std/Aeneas extraction boundary. -/
theorem generated_loop_success_decoded_product_sum
    (bytes : Slice U8) (scratch : Slice CutQM)
    (n : Usize) (iter : AspisR1S5PairCutRangeLoopTraceV1.Range)
    (pair out : AspisR1S5PairCutRangeLoopTraceV1.PairDot)
    (hend : iter.end.val = n.val)
    (hstart : iter.start.val ≤ n.val)
    (hloop : AspisR1WeightsPairCut.weights.push_byte_products_loop
      iter pair bytes scratch = .ok (.Ok (), out))
    (hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c0.sums)
    (hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource pair).count.val (stateToSource pair).c1.sums) :
    ∃ indices xs currentOut,
      CallbackRangeTrace (readerBody actualPairDecoder) bytes scratch n iter pair indices out ∧
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
  have hrun : AspisR1S5PairCutRangeLoopTraceV1.run
      (readerBody actualPairDecoder) bytes scratch iter pair = .ok (.Ok (), out) := by
    rw [← AspisR1S5PairCutActualGeneratedBodyV1.generated_loop_eq_range_run
      bytes scratch iter pair]
    exact hloop
  exact emitted_reader_run_decoded_product_sum bytes scratch n iter pair out
    hend hstart hrun hinv0 hinv1

#print axioms generated_loop_success_decoded_product_sum
end AspisR1S5PairCutActualGeneratedLoopProductV1
