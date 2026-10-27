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

theorem accepted {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ parts,D.digest hash parts=ok (MultiproofConePhysicalTransport.rawOracle H parts))
    (proof : Slice U8) (root : Array U8 32#usize) (kind lo n slot d : Usize)
    (keys : Array U64 16#usize) (idx outIdx : Indices) (val outVal : Values)
    (success : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body Port4B_Install.leaves
      D proof root kind hash lo n slot keys idx val d n=ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ supplied : Slice U8,
      Port4B_Install.leaves.op10 D hash Port3_NativeBatchBody.multiproof.Arity.Two
        root idx val d supplied=ok (true,outIdx,outVal) ∧
      (eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root kind hash
        lo n slot keys idx val d n))).1=
        (eval H (SdkC_Oracle.program (Port9OR_P6Verify.code root ⟨idx,val,d,0#usize⟩ supplied))).1 := by
  obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,
    fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=
    Port4B_TailReads.reads Port4B_Install.leaves D hash proof root kind lo n slot d keys idx outIdx val outVal success
  refine ⟨supplied,verifyRead,?_⟩
  have verifyValue : (eval H (SdkC_Oracle.program (Port9OR_BatchStep.verify root idx val d supplied))).2=
      ok (true,outIdx,outVal) := by
    rw [F3Q_IdealCode.value D hash H law,Port9OR_BatchStep.verify_source Port4B_Install.leaves]
    exact verifyRead
  unfold Port9OR_BatchStep.body
  simp only [lt_self_iff_false,if_false]
  simp only [Bind.bind,CheckpointBytes5Effect.bind,CheckpointBytes5Effect.liftResult,
    Port9OR_BatchStep.ops,Port3_BatchStd.install,frontRead,countRead,Port3_BatchStd.okOr,
    core.result.Result.Insts.CoreOpsTry.branch,nodeRead,capRead,lift,fit,if_false,
    paddingRead,chunksRead,scanRead,prefixRead]
  simp only [F3Q_CodeEval.bind_eval,verifyValue,Pure.pure,SdkC_Oracle.program,eval,List.append_nil]
  unfold Port9OR_BatchStep.verify
  exact F3Q_CodeLog.done_tail H _ _

#print axioms accepted
end AspisR1.F3Q_TerminalLog
end
