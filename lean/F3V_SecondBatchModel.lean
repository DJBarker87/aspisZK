import F3V_FirstBatchModel
import F3V_WriterCall
import SdkD_SecondModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SecondBatchModel
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem accepted {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (p : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse (bytesOf e.proof.val)=some p)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (q : Fin 22 → Fin 262144)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data q rho) :
    (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).2=true := by
  obtain ⟨p2,a2,root,view,read,range,copy,batch⟩ := F3V_SecondRun.accepted c (D2 c H) ()
    e.pub e.proof e.saved.deref e.second
  rw [←F3V_DigestCompatibility.same c H] at read batch
  have len := F3V_EvidenceCalls.length c B s H e
  have wire := (OraclePortCompactDraft.parse_header _ _ parser).2
  exact SdkD_SecondModel.indexed (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl) H H
    (F3V_DigestCompatibility.realization H) (F3U_Oracle.syscall H)
    e.proof e.proof e.pub e.pub e.saved.deref len len e.saved c.reserved
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.run.p p2
    (Tx1Q_Carriers.accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) a2
    _ e.run.scratch (F3V_EvidenceCalls.preparation c B s H e) root view range copy
    _ p parser wire wire data rho q prepare (F3V_WriterCall.same c B s H e) rfl read batch

#print axioms accepted
end AspisR1.F3V_SecondBatchModel
end
