import RPz7_F3N_WriterOnRun
import RPz7_F3N_SameOracle
import RPz7_SAP_PrepareOwner
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_SaveOnRun
open Aeneas Aeneas.Std Result AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Tx1Q_Carriers

theorem saved {C Hash : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo (F3M_CircleSource.install B) std)
      reserved query geo D hash semantic pub proof split saved)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (same : currentPrepared out=run.p) :
    saved=Tx2N_Reader.writer H (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf pub.val)
      (F3L_SourcePrepared.numeric out)
      (CheckpointBytes5Output.accumulator (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) :=
  (F3N_WriterOnRun.saved _ reserved query geo D hash semantic pub proof split saved run
    (SAP_PrepareOwner.installed (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
    ports H oracle out same).2

#print axioms saved
end AspisR1.SAP_SaveOnRun
end
