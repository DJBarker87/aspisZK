import F3V_SecondBatchModel
import AuS1_Context
import SdkD_BatchUnion
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Authenticated
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem recovered {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) (prior : Program Bytes State Unit)
    (p : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse (bytesOf e.proof.val)=some p) :
    let trace := (eval H prior).1 ++ AuS1_Recovery.log
      (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std (D1 c H)
      (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero)
    ∃ frame, FS2.Duplex.Read trace frame ∧
      BinRawByteCollisionTargets.pred 3 frame=some (OraclePortBatchDraft.committedRoot p 2) ∧
      ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
        (q : Fin 22 → Fin 262144),
        Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data q rho →
        AuS1_Finish.Collision H trace p q ∨
          ∀ pos,pos<22 → OraclePortAllSelectedRecoveryC6.recovered trace frame p 2
            (OraclePortSelectedDraft.index q 2 pos)=some (OraclePortPackedChoiceC4.payload p 2 pos) := by
  obtain ⟨frame,read,target,recover⟩ := AuS1_Context.authenticated prior
    (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std (D1 c H)
    (F3U_Oracle.hashv H) (fun _ _=>rfl) (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof ()
    _ e.run.scratch e.run.p (F3V_EvidenceCalls.preparation c B s H e) p parser H H
    (F3V_DigestCompatibility.realization H) (F3U_Oracle.syscall H)
  refine ⟨frame,read,target,?_⟩
  intro data rho q prepare
  exact recover q (SdkD_BatchUnion.accepted H p q
    (F3V_FirstBatchModel.accepted c B s H e p parser data rho q prepare)
    (F3V_SecondBatchModel.accepted c B s H e p parser data rho q prepare))

#print axioms recovered
end AspisR1.F3V_Authenticated
end
