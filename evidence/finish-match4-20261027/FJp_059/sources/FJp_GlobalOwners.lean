import FIp_GlobalOwners
import F3V_Checkpoint
import FJp_Remaining
import FGl_PreparedAt
import SAG_NativeFull
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_GlobalOwners
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Retained pair and semantic owner families in exactly the original scope. -/
def Owners {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Prop :=
  ∀ (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
    FGl_PreparedAt.At c B s H e i p q data →
    Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
      (D2 c H) () e.pub e.proof e.saved.deref t →
    SAG_NativeFull.Shape (Tx2N_Execution.control
      (Tx2I_Install.stage (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish)
      c.reserved c.query c.geometry) e.proof t →
    ∀ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
      FJp_Remaining.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data

theorem of_original {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FGl_PreparedAt.Owners c B) : Owners c B := by
  intro s H e i p q data t atPrepared calls shape x
  have h := old s H e i p q data t atPrepared calls x
  exact ⟨h.1.pair,h.2.2.1⟩

/-- Every old satisfying owner instance survives the premise removal. -/
theorem weaken {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FIp_GlobalOwners.Owners c B) : Owners c B := by
  intro s H e i p q data t atPrepared calls shape x
  have h := old s H e i p q data t atPrepared calls shape x
  exact ⟨h.1,h.2.2⟩
#print axioms weaken

/-- SAME-context law to be supplied by the checked source derivation, never a top premise. -/
def Matching {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Prop :=
  ∀ (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs),
    FGl_PreparedAt.At c B s H e i p q data →
    ∀ prior : Program Bytes State Unit,
      AuS1_Finish.Collision H (F3V_Checkpoint.trace c B s H e prior) p q ∨
      ∀ j : Fin 22,MatchingSupport.match0 data.data (q j)

#print axioms of_original
end AspisR1.FJp_GlobalOwners
end
