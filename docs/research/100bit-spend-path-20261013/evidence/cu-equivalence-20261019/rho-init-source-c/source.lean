import AspisR1RhoInit.Funs

/-! Complete new-wrapper interpretation: its allocation/error/constructor code
is the emitted wrapper, and its original for-block uses the inherited Vec,
slice-iterator, Zip and loan writeback definitions. The heap API contract and
sufficient resources remain separate obligations, not an equivalence axiom.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoInitSource
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoPushStep
variable [InitAllocation]

def sourceFor (raw : alloc.vec.Vec Raw4) (weights : Slice field.QM31) :
    Result (alloc.vec.Vec Raw4) := do
  let (slice,vecBack) := alloc.vec.Vec.deref_mut raw
  let (iter,iterBack) ← core.slice.Slice.iter_mut slice
  let shared ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter weights
  let last ← loop (CuSavingsZipFill.body CuSavingsRhoZipInitialization.assignment)
    (core.iter.adapters.zip.Zip.mk iter shared)
  .ok (vecBack (iterBack last.fst))

theorem sourceFor_eq (raw : alloc.vec.Vec Raw4) (weights : Slice field.QM31) :
    sourceFor raw weights = verifier.initialize_weights raw weights := by
  simp only [sourceFor,alloc.vec.Vec.deref_mut,core.slice.Slice.iter_mut,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_tc_ok,
    verifier.initialize_weights,CuSavingsRhoZipInitialization.initializeRows,CuSavingsZipFill.fill]
  rfl

def sourceNew (weights : Slice field.QM31) :
    Result (core.result.Result verifier.BatchedWeights verifier.Error) := do
  let i := Slice.len weights
  let a := Array.repeat 4#usize 0#u64
  let r ← r0.heap.filled (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) i a
  let r1 ← core.result.Result.map_err
    verifier.BatchedWeights.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let val1 ← sourceFor val weights
    .ok (core.result.Result.Ok {«raw»:=val1,terms:=0#usize})
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.BatchedWeights (core.convert.FromSame verifier.Error) residual

theorem source_eq (weights : Slice field.QM31) :
    sourceNew weights = verifier.BatchedWeights.new weights := by
  simp only [sourceNew,verifier.BatchedWeights.new,sourceFor_eq]
  rfl

def heapResult (weights : Slice field.QM31) :
    Result (core.result.Result (alloc.vec.Vec Raw4) r0.Error) :=
  r0.heap.filled (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
    (Slice.len weights) (Array.repeat 4#usize 0#u64)

def heapOutcome (weights : Slice field.QM31)
    (out : core.result.Result (alloc.vec.Vec Raw4) r0.Error) :
    core.result.Result verifier.BatchedWeights verifier.Error :=
  match out with
  | .Err _ => .Err .Allocation
  | .Ok _ => .Ok (initialState weights)

theorem source_outcome (weights : Slice field.QM31)
    (hsize : ∀ raw,heapResult weights = .ok (.Ok raw) →
      raw.val.length = weights.val.length) :
    sourceNew weights = (do let out ← heapResult weights;.ok (heapOutcome weights out)) := by
  rw [source_eq]
  unfold verifier.BatchedWeights.new
  change (do
    let r ← heapResult weights
    let r1 ← core.result.Result.map_err
      verifier.BatchedWeights.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val => do
      let val1 ← verifier.initialize_weights val weights
      .ok (core.result.Result.Ok {«raw»:=val1,terms:=0#usize} : core.result.Result verifier.BatchedWeights verifier.Error)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.BatchedWeights (core.convert.FromSame verifier.Error) residual) = _
  cases ha : heapResult weights with
  | fail error => simp only [ha,bind_tc_fail]
  | div => simp only [ha,bind_tc_div]
  | ok result =>
    cases result with
    | Err error =>
      simp only [ha,bind_tc_ok,core.result.Result.map_err,
        AspisR1PublicPreparation.core.result.Result.map_err,
        verifier.BatchedWeights.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        verifier.BatchedWeights.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,heapOutcome]
      rfl
    | Ok raw =>
      have hi := CuSavingsRhoZipInitialization.initialize_eq raw weights (hsize raw ha)
      simp only [ha,bind_tc_ok,core.result.Result.map_err,
        AspisR1PublicPreparation.core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch,verifier.initialize_weights,hi,heapOutcome]
      rfl

#print axioms sourceFor_eq
#print axioms source_eq
#print axioms source_outcome
end AspisR1.CuSavingsRhoInitSource
