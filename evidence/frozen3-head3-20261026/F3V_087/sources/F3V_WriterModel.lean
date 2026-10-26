import F3V_CheckpointOracle
import F3N_WriterOnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_WriterModel
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem saved {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (same : AspisR1CurrentCaller.InstalledPreparation.currentPrepared out=e.run.p) :
    e.saved=Tx2N_Reader.writer H (bytesOf e.proof.val) (bytesOf e.pub.val)
      (F3L_SourcePrepared.numeric out)
      (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator
        {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩})) := by
  have oracle := F3V_CheckpointOracle.oracle c H
  rw [←F3V_DigestCompatibility.same c H] at oracle
  exact (F3N_WriterOnRun.saved _ c.reserved c.query c.geometry (D1 c H) ()
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved e.run owner ports
    H oracle out same).2

#print axioms saved
end AspisR1.F3V_WriterModel
end
