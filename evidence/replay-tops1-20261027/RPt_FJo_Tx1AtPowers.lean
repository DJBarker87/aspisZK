import RPt_FJo_Tx1Powers
import RPt_FJl_PreparedAtValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_Tx1AtPowers
open Aeneas Aeneas.Std Result
open DrvC_Installation F3V_RunEvidence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- All TX1 coefficients use the literal gamma in the original At context. -/
theorem value {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : F3T_ByteCarrier.Submission)
    (H : Bytes → State) (e : Evidence c B s H) (i : F3_Model.Input)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (atPrepared : FGl_PreparedAt.At c B s H e i p q data) :
    let g := FIp_DotsAdapter.toArray (Tx1Q_Carriers.arr Tx1Q_Carriers.e e.run.scratch)
    FIo_ArrayCanon.Holds g ∧ ∀ l : Fin 29,FIp_ArrayValue.value g l.val=data.data.gamma^l.val := by
  have source := FJo_Tx1Powers.value (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    c.boundaries c.std (D1 c H) () (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
    e.pub e.proof 10#usize e.saved e.run
  have literal := (FJl_PreparedAtValues.value c B s H e i p q data atPrepared).1
  exact ⟨source.1,fun l=>by rw [source.2 l,literal]⟩
#print axioms value
end AspisR1.FJo_Tx1AtPowers
end
