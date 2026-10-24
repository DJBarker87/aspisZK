import Port9OR_P6Verify
import Port4B_Install

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchStep
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2 CheckpointBytes5Effect

abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize
abbrev Next := Indices × Values × Usize × Usize
abbrev Out := Indices × Values × Option (core.result.Result Unit verifier.Error)

def ops (base : Port3_NativeBatchBody.Ops) := Port3_BatchStd.install (Port4B_VerifyInstall.install base)

def verify (root : Digest) (idx : Indices) (val : Values) (n : Usize) (nodes : Slice U8) :
    Code (Bool × Indices × Values) := do
  let (accepted,out) ← Port9OR_P6Verify.code root ⟨idx,val,n,0#usize⟩ nodes
  pure (accepted,out.idx,out.val)

theorem verify_source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (root : Digest)
    (idx : Indices) (val : Values) (n : Usize) (nodes : Slice U8) :
    erase D hash (verify root idx val n nodes)=
      (ops base).op10 D hash .Two root idx val n nodes := by
  simp only [verify,erase_bind,erase_pure,Port9OR_P6Verify.source]
  rfl

def body (base : Port3_NativeBatchBody.Ops) {Hash : Type}
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
      let leaf ← Port4B_LeafCode.code tree q
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

theorem source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) :
    erase D hash (body base D proof root tree hash lo n slot keys idx val d pos)=
      Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body (ops base)
        D proof root tree hash lo n slot keys idx val d pos := by
  simp only [body,erase_bind,erase_lift,erase_pure,erase_ite,verify_source]
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  repeat
    first
    | rfl
    | (fail_if_no_progress simp only [erase_bind,erase_pure,erase_lift,erase_ite,CheckpointBytes5Effect.bind,verify_source])
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value success)
    | cases_type Prod
    | cases_type core.ops.control_flow.ControlFlow
    | (split <;> (try simp_all only [if_true,if_false]))
  all_goals try simp only [erase_bind,erase_pure,erase_lift,verify_source]
  all_goals rfl

#print axioms verify_source
#print axioms source
end AspisR1.Port9OR_BatchStep
end
