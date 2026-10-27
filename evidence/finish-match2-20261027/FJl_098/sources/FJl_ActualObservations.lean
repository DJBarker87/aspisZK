import FJl_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ActualObservations
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Every opening, fold, inverse, alpha and successful comparison comes from
its actual iteration of ONE accepted two-phase execution. -/
theorem accepted {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : F3T_ByteCarrier.Submission) (H : Bytes → State) (e : Evidence c B s H) :
    ∃ (p2 : verifier.Prepared) (saved2 : verifier.Accumulator)
      (g2 : Array FIp_DotsAdapter.E 29#usize) (geo2 : verifier.QueryGeometry),
      Port4A_ReaderInstall.reader c.reserved (D2 c H) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p2,saved2)) ∧
      saved2.next=10#usize ∧ Tx2N_Powers.powers 29#usize p2.gamma=ok g2 ∧
      ∀ j : Fin 22, ∃ a0 a1 b0 b1, a0.next.val=j.val ∧
        Nonempty (Port4C_QueryValues.Observation
          (if j.val<10 then Tx1Q_QueryBridge.leaves c.query else
            Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install c.query)))
          e.proof (if j.val<10 then prepared e.run.p else p2) a0 a1
          (if j.val<10 then arr Tx1Q_Carriers.e e.run.scratch else g2) none
          (if j.val<10 then geometry e.run.geometry else geo2) b0 b1) := by
  obtain ⟨p2,saved2,g2,geo2,hr,hn,hg,calls⟩ := FJl_PairExtraction.accepted c B s H e
  refine ⟨p2,saved2,g2,geo2,hr,hn,hg,?_⟩
  intro j
  exact FJl_Observation.reached _ e.proof _ _ _ j.val (calls j)
#print axioms accepted
end AspisR1.FJl_ActualObservations
end
