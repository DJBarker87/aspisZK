import F3Q_BatchValue
import F3Q_CodeLog
import Port4B_TailReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TerminalLog
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem of_reads {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (proof : Slice U8) (root : Array U8 32#usize) (kind lo n slot d : Usize)
    (keys : Array U64 16#usize) (idx outIdx : Indices) (val outVal : Values)
    (front : Slice U32) (count cap : Usize) (nodes padding supplied : Slice U8)
    (ce after : core.slice.iter.ChunksExact U8)
    (frontRead : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32)) idx {«end»:=d}=ok front)
    (countRead : (Port9OR_BatchStep.ops Port4B_Install.leaves).op11 Port3_NativeBatchBody.multiproof.Arity.Two front=ok (some count))
    (nodeRead : (Port9OR_BatchStep.ops Port4B_Install.leaves).op3 proof slot=ok nodes)
    (capRead : Array.index_usize (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) slot=ok cap)
    (fit : ¬count>cap)
    (paddingRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) nodes {start:=Usize.wrapping_mul 32#usize count}=ok padding)
    (chunksRead : core.slice.Slice.chunks_exact padding 8#usize=ok ce)
    (scanRead : (Port9OR_BatchStep.ops Port4B_Install.leaves).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
      (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool (Port9OR_BatchStep.ops Port4B_Install.leaves) D) ce ()=ok (false,after))
    (prefixRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) nodes {«end»:=Usize.wrapping_mul 32#usize count}=ok supplied)
    (verifyRead : Port4B_Install.leaves.op10 D hash Port3_NativeBatchBody.multiproof.Arity.Two root idx val d supplied=ok (true,outIdx,outVal)) :
    (eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root kind hash
      lo n slot keys idx val d n))).1=
      (eval H (SdkC_Oracle.program (Port9OR_P6Verify.code root ⟨idx,val,d,0#usize⟩ supplied))).1 := by
  have verifyValue : (eval H (SdkC_Oracle.program (Port9OR_BatchStep.verify root idx val d supplied))).2=
      ok (true,outIdx,outVal) := by
    rw [F3Q_IdealCode.value D hash H law,Port9OR_BatchStep.verify_source Port4B_Install.leaves]
    exact verifyRead
  have okOr : (Port9OR_BatchStep.ops Port4B_Install.leaves).op1 (some count) verifier.Error.Merkle=ok (.Ok count) := rfl
  have caps : (Port9OR_BatchStep.ops Port4B_Install.leaves).op12=ok (Array.make 6#usize [146#usize,146#usize,128#usize,172#usize,172#usize,150#usize]) := rfl
  unfold Port9OR_BatchStep.body
  simp only [lt_self_iff_false,if_false]
  simp only [Bind.bind,CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,
    frontRead,countRead,okOr,caps,
    core.result.Result.Insts.CoreOpsTry.branch,nodeRead,capRead,lift,fit,if_false,
    paddingRead,chunksRead,scanRead,prefixRead,SdkC_Oracle.program,Bool.false_eq_true,if_false]
  simp only [F3Q_CodeEval.bind_eval,verifyValue,Pure.pure,SdkC_Oracle.program,eval,List.append_nil]
  unfold Port9OR_BatchStep.verify
  exact F3Q_CodeLog.done_tail H _ _

#print axioms of_reads
end AspisR1.F3Q_TerminalLog
end
