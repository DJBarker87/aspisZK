import RPt_BEl_LeafReference
import RPt_BEl_CodeCongr
import Port9OR_BatchStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_BatchStep
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out ops verify)

/-- Exact source-control copy, parameterizing only the leaf expression.
The owned Rust reference checks value before salt; leaf replacement is proved
observationally, including all pure/partial failures, rather than assumed. -/
def bodyWith (leaf : Usize → Slice U8 → SdkC_Source.Code Digest) (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (root : Digest) (tree : Usize) (hash : Hash)
    (lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d key_position : Usize) : Code (ControlFlow Next Out) :=
  let ops := ops base
  let s := slot
  do
    if key_position < n
    then
      let key ← liftResult (
        ops.op9 keys key_position
        )
      let key_position1 ← liftResult (
        lift (Std.Usize.wrapping_add key_position 1#usize)
        )
      let i ← liftResult (
        lift (Std.U64.wrapping_shr key 8#u32)
        )
      let index ← liftResult (
        lift (UScalar.cast .U32 i)
        )
      let i1 ← liftResult (
        lift (key &&& 255#u64)
        )
      let i2 ← liftResult (
        lift (UScalar.cast .Usize i1)
        )
      let i3 ← liftResult (
        lift (Std.Usize.wrapping_add lo i2)
        )
      let q ← liftResult (
        ops.op2 proof i3
        )
      let leaf ← leaf tree q
      if d > 0#usize
      then
        let i4 ← liftResult (
          lift (Std.Usize.wrapping_sub d 1#usize)
          )
        let b ← liftResult (
          ops.op8 idx i4 index
          )
        if b
        then
          let i5 ← liftResult (
            lift (Std.Usize.wrapping_sub d 1#usize)
            )
          let b1 ← liftResult (
            ops.op7 val i5 leaf
            )
          if b1
          then pure (cont (idx, val, d, key_position1))
          else
            pure (done (idx, val, some (core.result.Result.Err
              verifier.Error.Merkle)))
        else
          let idx1 ← liftResult (
            Array.update idx d index
            )
          let val1 ← liftResult (
            Array.update val d leaf
            )
          let d1 ← liftResult (
            lift (Std.Usize.wrapping_add d 1#usize)
            )
          pure (cont (idx1, val1, d1, key_position1))
      else
        let idx1 ← liftResult (
          Array.update idx d index
          )
        let val1 ← liftResult (
          Array.update val d leaf
          )
        let d1 ← liftResult (
          lift (Std.Usize.wrapping_add d 1#usize)
          )
        pure (cont (idx1, val1, d1, key_position1))
    else
      let s1 ← liftResult (
        core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) idx
        { «end» := d }
        )
      let o ← liftResult (
        ops.op11 Port3_NativeBatchBody.multiproof.Arity.Two s1
        )
      let r ← liftResult (
        ops.op1 o verifier.Error.Merkle
        )
      let cf ← liftResult (
        core.result.Result.Insts.CoreOpsTry.branch r
        )
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let nodes ← liftResult (
          ops.op3 proof s
          )
        let a ← liftResult (
          ops.op12
          )
        let i ← liftResult (
          Array.index_usize a s
          )
        if val1 > i
        then pure (done (idx, val, none))
        else
          let i1 ← liftResult (
            lift (Std.Usize.wrapping_mul 32#usize val1)
            )
          let s2 ← liftResult (
            core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) nodes
            { start := i1 }
            )
          let ce ← liftResult (
            core.slice.Slice.chunks_exact s2 8#usize
            )
          let (b, _) ← liftResult (
            ops.op0
            (core.iter.traits.iterator.IteratorChunksExact Std.U8)
            ((Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool ops)
            aspis_coredigestDigest32Inst) ce ()
            )
          if b
          then pure (done (idx, val, none))
          else
            let i2 ← liftResult (
              lift (Std.Usize.wrapping_mul 32#usize val1)
              )
            let s3 ← liftResult (
              core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) nodes
              { «end» := i2 }
              )
            let (b1, idx1, val2) ← verify root idx val d s3
            if b1
            then pure (done (idx1, val2, some (core.result.Result.Ok ())))
            else pure (done (idx1, val2, none))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let _ ← liftResult (
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
          )
        pure (done (idx, val, none))

theorem original (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) :
    bodyWith Port4B_LeafCode.code base D proof root tree hash lo n slot keys idx val d pos =
      Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos := rfl

/-- Concrete whole step: every source head, duplicate branch, live scratch
write and actual tail is retained; the reference leaf's pure check order is
transported under its SAME continuation. No accepted-step premise is used. -/
theorem leaf_transport {S Hash : Type} (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (base : Port3_NativeBatchBody.Ops) (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) :
    BEl_CodeCongr.Equivalent call
      (bodyWith BEl_LeafReference.code base D proof root tree hash lo n slot keys idx val d pos)
      (Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos) := by
  rw [←original]
  by_cases active : pos < n
  · simp only [bodyWith,active,↓reduceIte]
    apply BEl_CodeCongr.bind_tail
    intro key
    apply BEl_CodeCongr.bind_tail
    intro nextPos
    apply BEl_CodeCongr.bind_tail
    intro shifted
    apply BEl_CodeCongr.bind_tail
    intro index
    apply BEl_CodeCongr.bind_tail
    intro low
    apply BEl_CodeCongr.bind_tail
    intro ordinal
    apply BEl_CodeCongr.bind_tail
    intro selected
    apply BEl_CodeCongr.bind_tail
    intro opening
    apply BEl_CodeCongr.bind_head
    intro state before
    exact BEl_LeafReference.observation call tree opening state before
  · simp only [bodyWith,active,↓reduceIte]
    intro state before
    rfl

#print axioms leaf_transport

#print axioms original
end AspisR1.BEl_BatchStep
end
