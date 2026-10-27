import FIp_GlobalOwners
import F3V_WriterModel
import F3N_ReaderNumeric
import FIp_Install
import SAP_PrepareOwner
import Tx1Q_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_GlobalFields
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence
attribute [local irreducible] QuadraticAlgebra.instInv

theorem fields {C : Type} (err : C) (base : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (s : Submission) (H : Bytes → State)
    (e : Evidence (FIp_Install.configuration err base r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r).boundaries s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness)
    (atPrepared : FGl_PreparedAt.At (FIp_Install.configuration err base r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r).boundaries s H e i p q data)
    (calls : Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base (FIp_Install.configuration err base r).stageBase))
      (FIp_Install.configuration err base r).finish (FIp_Install.configuration err base r).reserved
      (FIp_Install.configuration err base r).query (FIp_Install.configuration err base r).geometry
      (D2 (FIp_Install.configuration err base r) H) () e.pub e.proof e.saved.deref t) :
    ∃ (view : LiteralOpeningView.View) (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E),
      LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
        (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2))=some view ∧
      CheckpointBytes4SavedFields.BodyMatches t.p2 t.saved2
        (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context p data view)
          data.data (SelectedChallengeMap.rhoOf data.rho) q) am := by
  let c := FIp_Install.configuration err base r
  let B := (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r).boundaries
  obtain ⟨physical,stored,parser,queries,found,prepare,out,view,output,opening,numeric,log,guard⟩ := atPrepared
  have owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std) :=
    SAP_PrepareOwner.installed _ (FIp_Install.boundaries base.boundaries) (NP6_StdModel.calls r)
  have ports : Port5Q1_QueryPorts.SessionAPrimitives c.query := SAQ_Decoder.primitives (FIp_Install.select r base).query
  have saved := F3V_WriterModel.saved c B s H e owner ports out output
  rw [numeric] at saved
  have control := Tx1Q_Control.fields _ _ _ _ _ _ _ _ _ _ _ _ e.run
  have ten : (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
      {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩})).next=10 := control.2.2.1
  have fields := F3N_ReaderNumeric.saved_ten (Op5T_Concrete.stage (AuS1_Install.base c.stageBase))
    c.reserved c.query (D2 c H) () e.saved.deref e.proof e.pub e.saved t.p2 t.saved2 H
    _ _ _ _ ten rfl saved calls.1
  exact ⟨view,_,opening,fields.1⟩

#print axioms fields
end AspisR1.FJs_GlobalFields
end
