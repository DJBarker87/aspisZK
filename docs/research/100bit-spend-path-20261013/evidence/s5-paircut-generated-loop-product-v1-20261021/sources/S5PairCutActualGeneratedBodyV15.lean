import S5PairCutRangeLoopTraceV1
import S5PairCutTransparentReaderAdapterV1
import EbyKConcreteOpsInstanceV1
import AspisR1WeightsPairCut.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S5PairCutActualGeneratedBodyV1

open AspisR1S5PairCutRangeLoopTraceV1
open AspisR1S5PairCutLoopFoldV1
open AspisR1S5PairCutTransparentReaderV1
open AspisR1WeightsPairCutEbyKDotOpsV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=
  AspisR1S5EbyKConcreteOpsInstanceV1.sourceOps

/-- The generated PairCut body itself follows the source-model success branch
when its exact iterator, decoder-backed field read, scratch read, and installed
EbyK push succeed. The generated runtime overlay replaces only the three
external EbyK methods by the selected installed source ops and replaces the
unreachable decoder stub by the selected strict decoder. -/
theorem generated_body_matches_range_model_success_v12
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter iter1 : core.ops.range.Range Usize) (j : Usize)
    (pair pair1 : AspisR1WeightsPairCut.fast_pairing.EbyKDot)
    (value : AspisR1S5PairCutTransparentReaderV1.PairWide) (scalar : PairQM)
    (hnext : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = .ok (some j, iter1))
    (hread : readerBody actualPairDecoder bytes j = .ok value)
    (hscalar : Slice.index_usize scratch j = .ok scalar)
    (hpush : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
      pair value scalar = .ok (.Ok (), pair1)) :
    AspisR1WeightsPairCut.weights.push_byte_products_loop.body
      bytes scratch iter pair =
    AspisR1S5PairCutRangeLoopTraceV1.body (readerBody actualPairDecoder)
      bytes scratch (iter, pair) := by
  have hfield : AspisR1WeightsPairCut.weights.field bytes j = .ok value := by
    change readerBody actualPairDecoder bytes j = .ok value
    exact hread
  unfold AspisR1WeightsPairCut.weights.push_byte_products_loop.body
    AspisR1S5PairCutRangeLoopTraceV1.body
  simp [hnext, hfield, hscalar, hpush,
    AspisR1WeightsPairCut.core.result.Result.map_err,
    Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    AspisR1WeightsPairCut.weights.push_byte_products.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
    AspisR1S5PairCutRangeLoopTraceV1.body,
    AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
    AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt,
    AspisR1S5PairCutLoopFoldV1.pushByteProductsPostPush]
  rw [hread]
  simp only [Result.ok]
  rw [hpush]
  rfl

/-- Full one-step equality for the emitted body and its explicit Aeneas/Core
ControlFlow adapter. This includes all error and end-of-range branches. -/
theorem generated_body_eq_range_body_all
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter : core.ops.range.Range Usize)
    (pair : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    AspisR1WeightsPairCut.weights.push_byte_products_loop.body
      bytes scratch iter pair =
    AspisR1S5PairCutRangeLoopTraceV1.body
      (readerBody actualPairDecoder) bytes scratch (iter, pair) := by
  have hfieldfun : AspisR1WeightsPairCut.weights.field =
      readerBody actualPairDecoder := by
    funext b i
    rfl
  unfold AspisR1WeightsPairCut.weights.push_byte_products_loop.body
    AspisR1S5PairCutRangeLoopTraceV1.body
  rw [hfieldfun]
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp [hn, AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith]
  | div => simp [hn, AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith]
  | ok pairNext =>
      rcases pairNext with ⟨o, iter1⟩
      cases o with
      | none => simp [hn, AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith]
      | some j =>
          cases hr : readerBody actualPairDecoder bytes j with
          | fail e => simp [hn, hr, AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
              AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt]
          | div => simp [hn, hr, AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
              AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt]
          | ok value =>
              cases hs : Slice.index_usize scratch j with
              | fail e => simp [hn, hr, hs,
                  AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
                  AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt]
              | div => simp [hn, hr, hs,
                  AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
                  AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt]
              | ok scalar =>
                  cases hp : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
                      pair value scalar with
                  | fail e => simp [hn, hr, hs, hp,
                      AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
                      AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt]
                  | div => simp [hn, hr, hs, hp,
                      AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
                      AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt]
                  | ok out =>
                      rcases out with ⟨r, pair1⟩
                      cases r <;> simp [hn, hr, hs, hp,
                        AspisR1WeightsPairCut.core.result.Result.map_err,
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        AspisR1WeightsPairCut.weights.push_byte_products.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
                        AspisR1S5PairCutLoopFoldV1.pushByteProductsBodyWith,
                        AspisR1S5PairCutLoopFoldV1.pushByteProductsAfterNextAt,
                        AspisR1S5PairCutLoopFoldV1.pushByteProductsPostPush]

/-- The generated whole range-loop and the selected reader range model share
the exact same Aeneas loop after substituting the pointwise body theorem. -/
theorem generated_loop_eq_range_run
    (bytes : Slice U8) (scratch : Slice PairQM)
    (iter : core.ops.range.Range Usize)
    (pair : AspisR1WeightsPairCut.fast_pairing.EbyKDot) :
    AspisR1WeightsPairCut.weights.push_byte_products_loop
      iter pair bytes scratch =
    AspisR1S5PairCutRangeLoopTraceV1.run
      (readerBody actualPairDecoder) bytes scratch iter pair := by
  change Aeneas.Std.loop
      (fun s => AspisR1WeightsPairCut.weights.push_byte_products_loop.body
        bytes scratch s.1 s.2) (iter, pair) =
    Aeneas.Std.loop
      (AspisR1S5PairCutRangeLoopTraceV1.body
        (readerBody actualPairDecoder) bytes scratch) (iter, pair)
  have hbody :
      (fun s : core.ops.range.Range Usize × AspisR1WeightsPairCut.fast_pairing.EbyKDot =>
        AspisR1WeightsPairCut.weights.push_byte_products_loop.body
          bytes scratch s.1 s.2) =
      AspisR1S5PairCutRangeLoopTraceV1.body
        (readerBody actualPairDecoder) bytes scratch := by
    funext s
    exact generated_body_eq_range_body_all bytes scratch s.1 s.2
  rw [hbody]

#print axioms generated_loop_eq_range_run

#print axioms generated_body_eq_range_body_all

#print axioms generated_body_matches_range_model_success_v12
end AspisR1S5PairCutActualGeneratedBodyV1
