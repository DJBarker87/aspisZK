import RPu_FJo_AlphaPersistence
import RPu_FJo_Tx1AlphaCanonical
import RPu_FJl_PreparedAtValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ReaderLiteralAlpha
open Aeneas Aeneas.Std Result AspisR1Stage2
open DrvC_Installation F3V_RunEvidence Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Every resumed alpha0 read uses the SAME original literal alpha0. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) (i : F3_Model.Input)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At c B s H e i p q data)
    (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (reader : Port4A_ReaderInstall.reader c.reserved (D2 c H) e.saved.deref e.proof e.pub .S2 ()=ok (.Ok (p1,a1)))
    (alpha1 : Stage2Finish.E) (read1 : Array.index_usize p1.alpha 0#usize=ok alpha1) :
    CheckpointBytes5Output.ofE alpha1=data.data.alpha0 := by
  let p0 := prepared e.run.p
  obtain ⟨alpha0,read0,cell⟩ := WP.spec_imp_exists (Array.index_usize_spec p0.alpha 0#usize
    (by change (0#usize).val<p0.alpha.val.length;rw [p0.alpha.property];decide))
  have canonical := FJo_Tx1AlphaCanonical.value (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    c.boundaries c.std (D1 c H) () (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
    e.pub e.proof 10#usize e.saved e.run alpha0 read0
  have write : Port3_CheckpointInstall.writer (D2 c H) p0
      (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) e.proof e.pub ()=ok e.saved := e.run.writer_call
  have source := Port4A_ReaderInstall.accepted_source c.stageBase c.reserved (D2 c H) ()
    e.saved.deref e.proof e.pub .S2 p1 a1 reader
  have same := FJo_AlphaPersistence.value c.reserved (D2 c H) p0 p1
    (accumulator {e.run.out with weights:=⟨e.run.flushed.val,e.run.flushed.property⟩}) a1
    e.saved.deref e.proof e.pub e.proof e.pub () e.saved alpha0 alpha1 read0 read1 canonical write rfl source
  exact same.trans ((FJl_PreparedAtValues.value c B s H e i p q data atPrepared).2 alpha0 read0)
#print axioms value
end AspisR1.FJo_ReaderLiteralAlpha
end
