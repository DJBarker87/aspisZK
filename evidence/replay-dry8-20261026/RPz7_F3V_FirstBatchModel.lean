import RPz7_F3V_EvidenceCalls
import RPz7_SdkD_FirstModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_FirstBatchModel
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
    (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true := by
  exact SdkD_FirstModel.indexed (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
    c.boundaries c.std (F3U_Oracle.hashv H) (D1 c H) (fun _=>rfl) H H
    (F3V_DigestCompatibility.realization H) (F3U_Oracle.syscall H)
    e.proof (F3V_EvidenceCalls.length c B s H e) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
    e.run.p _ e.run.scratch (F3V_EvidenceCalls.preparation c B s H e)
    e.run.root e.rootView e.rootRange e.rootCopy _ p parser
    (OraclePortCompactDraft.parse_header _ _ parser).2 data rho q prepare e.run.batch_call

#print axioms accepted
end AspisR1.F3V_FirstBatchModel
end
