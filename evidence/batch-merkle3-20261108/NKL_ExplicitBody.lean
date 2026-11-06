import Port3_NativeBatchBody
set_option autoImplicit false
noncomputable section
namespace NKL_ExplicitBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
abbrev Ops := AspisR1.Port3_NativeBatchBody.Ops
abbrev multiproof.Arity := AspisR1.Port3_NativeBatchBody.multiproof.Arity
@[rust_loop_body]
def verifier.candidate.batch_tree_loop.body (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (proof : Slice Std.U8) (root : Array Std.U8 32#usize) (tree : Std.Usize)
  (hash : H) (lo : Std.Usize) (n : Std.Usize) (s : Std.Usize)
  (keys : Array Std.U64 16#usize) (idx : Array Std.U32 16#usize)
  (val : Array (Array Std.U8 32#usize) 16#usize) (d : Std.Usize)
  (key_position : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 16#usize) × (Array (Array Std.U8
    32#usize) 16#usize) × Std.Usize × Std.Usize) ((Array Std.U32 16#usize) ×
    (Array (Array Std.U8 32#usize) 16#usize) × ((core.result.Result
    Unit verifier.Error) × Bool)))
  := do
  if key_position < n
  then
    let key ← ops.op9 keys key_position
    let key_position1 ← lift (Std.Usize.wrapping_add key_position 1#usize)
    let i ← lift (Std.U64.wrapping_shr key 8#u32)
    let index ← lift (UScalar.cast .U32 i)
    let i1 ← lift (key &&& 255#u64)
    let i2 ← lift (UScalar.cast .Usize i1)
    let i3 ← lift (Std.Usize.wrapping_add lo i2)
    let q ← ops.op2 proof i3
    let leaf ←
      ops.op6 aspis_coredigestDigest32Inst hash tree q
    if d > 0#usize
    then
      let i4 ← lift (Std.Usize.wrapping_sub d 1#usize)
      let b ← ops.op8 idx i4 index
      if b
      then
        let i5 ← lift (Std.Usize.wrapping_sub d 1#usize)
        let b1 ← ops.op7 val i5 leaf
        if b1
        then ok (cont (idx, val, d, key_position1))
        else
          ok (done (idx, val, (core.result.Result.Err
            verifier.Error.Merkle, false)))
      else
        let idx1 ← Array.update idx d index
        let val1 ← Array.update val d leaf
        let d1 ← lift (Std.Usize.wrapping_add d 1#usize)
        ok (cont (idx1, val1, d1, key_position1))
    else
      let idx1 ← Array.update idx d index
      let val1 ← Array.update val d leaf
      let d1 ← lift (Std.Usize.wrapping_add d 1#usize)
      ok (cont (idx1, val1, d1, key_position1))
  else
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) idx
        { «end» := d }
    let o ← ops.op11 AspisR1.Port3_NativeBatchBody.multiproof.Arity.Two s1
    let r ← ops.op1 o verifier.Error.Merkle
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let nodes ← ops.op3 proof s
      let a ← ops.op12
      let i ← Array.index_usize a s
      if val1 > i
      then ok (done (idx, val, (core.result.Result.Err verifier.Error.Parse, true)))
      else
        let i1 ← lift (Std.Usize.wrapping_mul 32#usize val1)
        let s2 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) nodes
            { start := i1 }
        let ce ← core.slice.Slice.chunks_exact s2 8#usize
        let (b, _) ←
          ops.op0
            (core.iter.traits.iterator.IteratorChunksExact Std.U8)
            ((AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool ops)
            aspis_coredigestDigest32Inst) ce ()
        if b
        then ok (done (idx, val, (core.result.Result.Err verifier.Error.Parse, true)))
        else
          let i2 ← lift (Std.Usize.wrapping_mul 32#usize val1)
          let s3 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) nodes
              { «end» := i2 }
          let (b1, idx1, val2) ←
            ops.op10 aspis_coredigestDigest32Inst hash
              AspisR1.Port3_NativeBatchBody.multiproof.Arity.Two root idx val d s3
          if b1
          then ok (done (idx1, val2, (core.result.Result.Ok (), false)))
          else ok (done (idx1, val2, (core.result.Result.Err verifier.Error.Merkle, true)))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let returned ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
      ok (done (idx, val, (returned, true)))


end NKL_ExplicitBody
end
