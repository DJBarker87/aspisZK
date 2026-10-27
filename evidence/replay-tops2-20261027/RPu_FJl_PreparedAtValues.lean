import RPu_FJl_PreparedAlpha
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PreparedAtValues
open Aeneas Aeneas.Std Result
open DrvC_Installation F3V_RunEvidence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The owner's original SAME accepted-run context supplies gamma and alpha0;
no replacement Prepared identity is an input. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) (i : F3_Model.Input)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At c B s H e i p q data) :
    CheckpointBytes5Output.ofE (Tx1Q_Carriers.prepared e.run.p).gamma=data.data.gamma ∧
      ∀ a0,Array.index_usize (Tx1Q_Carriers.prepared e.run.p).alpha 0#usize=ok a0 →
        CheckpointBytes5Output.ofE a0=data.data.alpha0 := by
  obtain ⟨out,v,output,viewRead,numeric,log,guard⟩ := atPrepared.2.2.2.2.2.2
  constructor
  · rw [←output]
    exact FJl_PreparedGamma.value out p v q data numeric
  · intro a0 read
    rw [←output] at read
    exact FJl_PreparedAlpha.value out p v q data numeric a0 read
#print axioms value
end AspisR1.FJl_PreparedAtValues
end
