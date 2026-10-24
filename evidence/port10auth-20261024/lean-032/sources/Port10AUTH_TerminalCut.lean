import Port10AUTH_Verify
import Port9OR_BatchStep

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_TerminalCut
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open MultiproofConeRef
open Port9OR_BatchStep (Indices Values)

/-- Pure projection of the actual returned scratch preserves the full log on
all outcomes, including outer failure prefixes. -/
theorem map_log {A B X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (p : Code A) (f : A → B) :
    (Port9OR_Code.trace D hash (do let a ← p; pure (f a))).1=(Port9OR_Code.trace D hash p).1 := by
  rw [Port10AUTH_Trace.trace_bind]
  cases h : Port9OR_Code.trace D hash p with
  | mk log result => cases result <;> simp only [Port10AUTH_Leaf.pure_trace,List.append_nil]

/-- Count, complete padding scan and supplied-node prefix are actual accepted
source reads. The body emits exactly its reached verifier's observation. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Digest) (kind lo n slot : Usize)
    (keys : Array U64 16#usize) (s : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (success : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body (Port9OR_BatchStep.ops base)
      D proof root kind hash lo n slot keys s.idx s.val s.n n=ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ (front : Slice U32) (count cap : Usize) (nodes padding supplied : Slice U8)
      (ce after : core.slice.iter.ChunksExact U8),
      core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
        s.idx {«end»:=s.n}=ok front ∧
      (Port4B_VerifyInstall.install base).op11 Port3_NativeBatchBody.multiproof.Arity.Two front=ok (some count) ∧
      (Port4B_VerifyInstall.install base).op3 proof slot=ok nodes ∧
      Array.index_usize (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize])
        slot=ok cap ∧ ¬ count>cap ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
        nodes {start:=Usize.wrapping_mul 32#usize count}=ok padding ∧
      core.slice.Slice.chunks_exact padding 8#usize=ok ce ∧
      (Port9OR_BatchStep.ops base).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
        (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
          (Port9OR_BatchStep.ops base) D) ce ()=ok (false,after) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        nodes {«end»:=Usize.wrapping_mul 32#usize count}=ok supplied ∧
      (Port4B_VerifyInstall.install base).op10 D hash Port3_NativeBatchBody.multiproof.Arity.Two root s.idx s.val s.n supplied=
        ok (true,outIdx,outVal) ∧
      (Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n n)).1=
        (Port9OR_Code.trace D hash (Port9OR_BatchStep.verify root s.idx s.val s.n supplied)).1 := by
  obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,
    fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=
    Port4B_TailReads.reads (Port4B_VerifyInstall.install base) D hash proof root kind lo n slot s.n
      keys s.idx outIdx s.val outVal success
  refine ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,
    fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead,?_⟩
  unfold Port9OR_BatchStep.body
  rw [if_neg (lt_irrefl n)]
  have cr : (Port9OR_BatchStep.ops base).op11 Port3_NativeBatchBody.multiproof.Arity.Two front=ok (some count) := countRead
  have nr : (Port9OR_BatchStep.ops base).op3 proof slot=ok nodes := nodeRead
  simp only [Port10AUTH_Leaf.lift_bind,frontRead,cr]
  change (Port9OR_Code.trace D hash (show Code (ControlFlow Port9OR_BatchStep.Next Port9OR_BatchStep.Out) from do
    let nodes ← liftResult ((Port9OR_BatchStep.ops base).op3 proof slot)
    let a ← liftResult ((Port9OR_BatchStep.ops base).op12)
    let cap ← liftResult (Array.index_usize a slot)
    if count>cap then pure (.done (s.idx,s.val,none)) else do
      let i1 ← liftResult (lift (Usize.wrapping_mul 32#usize count))
      let s2 ← liftResult (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) nodes {start:=i1})
      let ce ← liftResult (core.slice.Slice.chunks_exact s2 8#usize)
      let (b,_) ← liftResult ((Port9OR_BatchStep.ops base).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
        ((Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
          (Port9OR_BatchStep.ops base)) D) ce ())
      if b then pure (.done (s.idx,s.val,none)) else do
        let i2 ← liftResult (lift (Usize.wrapping_mul 32#usize count))
        let s3 ← liftResult (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) nodes {«end»:=i2})
        let (b1,idx1,val1) ← Port9OR_BatchStep.verify root s.idx s.val s.n s3
        if b1 then pure (.done (idx1,val1,some (.Ok ()))) else pure (.done (idx1,val1,none)))).1=_
  simp only [Port9OR_BatchStep.ops,Port3_BatchStd.install] at scanRead
  simp only [Port10AUTH_Leaf.lift_bind,nodeRead,Port9OR_BatchStep.ops,Port3_BatchStd.install,
    capRead,if_neg fit,lift,paddingRead,chunksRead,scanRead,Bool.false_eq_true,if_false,prefixRead]
  change (Port9OR_Code.trace D hash (show Code (ControlFlow Port9OR_BatchStep.Next Port9OR_BatchStep.Out) from do
    let (b,idx,val) ← Port9OR_BatchStep.verify root s.idx s.val s.n supplied
    if b then pure (.done (idx,val,some (.Ok ()))) else pure (.done (idx,val,none)))).1=_
  exact map_log D hash _ (fun (out : Bool × Indices × Values) => (if out.1 then .done (out.2.1,out.2.2,some (.Ok ())) else .done (out.2.1,out.2.2,none) : ControlFlow Port9OR_BatchStep.Next Port9OR_BatchStep.Out))

#print axioms map_log
#print axioms accepted
end AspisR1.Port10AUTH_TerminalCut
end
