import RPt_FJl_PairExtraction
import RPu_FJo_PairPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PairSource
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- All actual source operands, retaining the resumed geometry constructor call. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) :
    ∃ (p2 : verifier.Prepared) (saved2 : verifier.Accumulator)
      (g2 : Array FIp_DotsAdapter.E 29#usize) (geo2 : verifier.QueryGeometry),
      Port4A_ReaderInstall.reader c.reserved (D2 c H) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,saved2)) ∧
      saved2.next=10#usize ∧ Tx2N_Powers.powers 29#usize p2.gamma=ok g2 ∧
      Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install c.geometry) p2.queries 10#usize 22#usize=ok (.Ok geo2) ∧
      ∀ j : Fin 22, ∃ a0 a1 b0 b1,a0.next.val=j.val ∧
        Port3_NativeQueryBody.verifier.candidate.query_values
          (if j.val<10 then Tx1Q_QueryBridge.leaves c.query else
            Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install c.query)))
          e.proof (if j.val<10 then prepared e.run.p else p2) a0
          (if j.val<10 then arr Tx1Q_Carriers.e e.run.scratch else g2) none
          (if j.val<10 then geometry e.run.geometry else geo2) b0=ok (.Ok (a1,b1)) := by
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ (D2 c H) () e.pub e.proof e.saved.deref none e.second
  have run : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
        c.reserved c.query c.geometry) (D2 c H) e.pub e.proof e.saved.deref () none=ok (.Ok ()) := common
  obtain ⟨p2,saved2,g2,geo2,pending,out,after,flushed,back,v,hr,hn,hg,hgeo,hpending,hquery,rest⟩ :=
    Tx2N_Execution.common _ c.reserved c.query c.geometry (D2 c H) () e.pub e.proof e.saved.deref run
  rw [hn] at hgeo
  refine ⟨p2,saved2,g2,geo2,hr,hn,hg,hgeo,?_⟩
  intro j
  by_cases early : j.val<10
  · simp only [if_pos early]
    exact FJl_Tx1Extraction.reached _ c.reserved c.query c.geometry (D1 c H) () _ e.pub e.proof 10#usize e.saved e.run ⟨j.val,early⟩
  · simp only [if_neg early]
    exact FJl_LoopExtraction.installed _ e.proof p2 saved2 out g2 geo2 pending after 22#usize
      (by rw [hn];decide) hquery j.val (by rw [hn];exact Nat.le_of_not_gt early) j.isLt
#print axioms value
end AspisR1.FJo_PairSource
end
