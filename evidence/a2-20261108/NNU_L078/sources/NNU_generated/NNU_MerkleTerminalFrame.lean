import NNU_MerkleNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleTerminalFrame
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchBody
open NKV_StepErasure NKV_LoopTransport
/-- The terminal expression keeps the actual operation slots abstract. -/
def code (base : Ops) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (hash : H) (s d : Usize)
 (idx : Indices) (val : Values) : Result (ControlFlow State CohortOut) := do
 let ops := Port3_BatchStd.install base
 let s1 ←
   core.array.Array.index (core.ops.index.IndexSlice
     (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) idx
     { «end» := d }
 let o ← ops.op11 multiproof.Arity.Two s1
 let r ← ops.op1 o verifier.Error.Merkle
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val1 =>
   let nodes ← ops.op3 proof s
   let a ← ops.op12
   let i ← Array.index_usize a s
   if val1 > i
   then ok (done (idx, val, none))
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
         ((verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool ops)
         aspis_coredigestDigest32Inst) ce ()
     if b
     then ok (done (idx, val, none))
     else
       let i2 ← lift (Std.Usize.wrapping_mul 32#usize val1)
       let s3 ←
         core.slice.index.Slice.index
           (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) nodes
           { «end» := i2 }
       let (b1, idx1, val2) ←
         ops.op10 aspis_coredigestDigest32Inst hash
           multiproof.Arity.Two root idx val d s3
       if b1
       then ok (done (idx1, val2, some (core.result.Result.Ok ())))
       else ok (done (idx1, val2, none))
 | core.ops.control_flow.ControlFlow.Break residual =>
   let _ ←
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       Unit (core.convert.FromSame verifier.Error) residual
   ok (done (idx, val, none))


theorem source (base : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (hash : H)
 (tree lo n slot d pos : Usize) (keys : Array U64 16#usize) (idx : Indices) (val : Values)
 (halt : ¬pos < n) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install base) D proof root tree hash lo n slot keys idx val d pos=
 code base D proof root hash slot d idx val := by
 unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
 rw [if_neg halt]
 rfl
theorem callback (left right : Ops) (D E : aspis_core.digest.Digest32 Unit) :
 verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
  (Port3_BatchStd.install left) D =
 verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
  (Port3_BatchStd.install right) E := by rfl

theorem count_slot (base : Ops) : (Port3_BatchStd.install base).op11=base.op11 := rfl
theorem node_slot (base : Ops) : (Port3_BatchStd.install base).op3=base.op3 := rfl
theorem verify_slot (base : Ops) : (Port3_BatchStd.install base).op10=base.op10 := rfl
#print axioms source
#print axioms callback
#print axioms count_slot
#print axioms node_slot
#print axioms verify_slot
end AspisR1.NNU_MerkleTerminalFrame
end
