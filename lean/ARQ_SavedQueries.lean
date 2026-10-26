import ARQ_QueryProjection
import F3V_WriterModel
import F3L_PreparedQueryPort
import F3X_PreparedAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_SavedQueries
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Decode the actual writer's saved query vector, before any clean/collision
case split. This fixes the observer even in the collision branch. -/
theorem decoded {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (same : AspisR1CurrentCaller.InstalledPreparation.currentPrepared out = e.run.p)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
    (q : Fin 22 → Fin 262144) (rho : OraclePortCheckpointAbiC5.K)
    (port : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data q rho) :
    OraclePortCheckpointPreparedC5.decodeQueries
      (OraclePortCompactDraft.slice (bytesOf e.saved.val) 320 88) = some q := by
  rw [F3V_WriterModel.saved c B s H e owner ports out same,ARQ_QueryProjection.writer_queries]
  change some (CheckpointBytes5Output.queries
    (Tx1Q_Carriers.prepared (AspisR1CurrentCaller.InstalledPreparation.currentPrepared out))) = some q
  rw [same,F3L_PreparedQueryPort.queries _ _ _ _ port]

#print axioms decoded
end AspisR1.ARQ_SavedQueries
end
