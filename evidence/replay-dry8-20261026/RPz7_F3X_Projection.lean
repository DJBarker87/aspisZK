import RPz7_F3V_PreparedFacts
import RPz7_F3L_PreparedQueryPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_Projection
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open F3T_ByteCarrier

abbrev Output := Submission × Option AspisR1CurrentCaller.verifier.Prepared

def project (out : Output) : OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144) :=
  ((OraclePortCompactDraft.parse out.1.stored).getD ⟨out.1.stored,[]⟩,
    match out.2 with
    | some p => CheckpointBytes5Output.queries (Tx1Q_Carriers.prepared p)
    | none => fun _=>0)

theorem on_prepared (s : Submission) (p : AspisR1CurrentCaller.verifier.Prepared)
    (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (parser : OraclePortCompactDraft.parse s.stored=some parsed)
    (port : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared p) data q rho) :
    project (s,some p)=(parsed,q) := by
  simp only [project,parser,Option.getD_some]
  exact congrArg (Prod.mk parsed) (F3L_PreparedQueryPort.queries _ _ _ _ port)

#print axioms on_prepared
end AspisR1.F3X_Projection
end
