import F3V_EvidenceCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_WriterCall
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem same {F C : Type} (c : Configuration F C) (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (s : Submission) (H : Bytes → State) (e : Evidence c B s H) :
    Port3_CheckpointInstall.writer (Tx1Q_Install.digest (D1 c H))
      (Tx1Q_Carriers.prepared e.run.p)
      (Tx1Q_Carriers.accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩})
      e.proof e.pub ()=ok e.saved := e.run.writer_call

#print axioms same
end AspisR1.F3V_WriterCall
end
