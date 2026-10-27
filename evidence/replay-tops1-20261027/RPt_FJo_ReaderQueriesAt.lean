import RPt_FJo_QueryRaw
import RPz8_FGl_PreparedAt
import RPz7_SdkD_CheckpointBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ReaderQueriesAt
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Actual resumed queries equal the original sampler values by checkpoint transport. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) (i : F3_Model.Input)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At c B s H e i p q data)
    (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (reader : Port4A_ReaderInstall.reader c.reserved (D2 c H) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p1,a1)))
    (j : Fin 22) : (Port5Q1_GeometryBinding.queryAt p1.queries j.val).val=(q j).val := by
  have write : Port3_CheckpointInstall.writer (D2 c H) (prepared e.run.p)
      (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) e.proof e.pub ()=ok e.saved := e.run.writer_call
  have source := Port4A_ReaderInstall.accepted_source c.stageBase c.reserved (D2 c H) ()
    e.saved.deref e.proof e.pub .S2 p1 a1 reader
  have fields := SdkD_CheckpointBinding.fields c.reserved (D2 c H) (prepared e.run.p) p1
    (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) a1
    e.saved.deref e.proof e.pub e.proof e.pub () e.saved write rfl source
  rw [fields.2.2]
  exact atPrepared.2.2.2.2.2.1.queries j.val j.isLt
#print axioms value
end AspisR1.FJo_ReaderQueriesAt
end
