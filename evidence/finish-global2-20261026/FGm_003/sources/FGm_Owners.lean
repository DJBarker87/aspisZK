import FIn_Finish
import FGl_PreparedAt
import F3V_RunEvidence
import FGl_FinishLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_Owners
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Five retained global families: Pair, matching and three semantic endpoints.
No extra success, shape or parser restriction is introduced. -/
def Holds {W : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps W)
    (v : AspisR1Stage2.verifier.View) (p : AspisR1Stage2.verifier.Prepared)
    (q : Fin 22 → Fin 262144) (parsed : OraclePortCompactDraft.Parsed)
    (tr : RawCutTranscriptRun.ErasedPrefix) (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FIn_Finish.PairMeaning finish v p input.data ∧
  (∀ j,MatchingSupport.match0 input.data (q j)) ∧
  R3SemanticRemainingJoins.EquationEndpoint input.decoded
    (OraclePortStoredDecisionDraftC4.typedRows parsed q tr) input.data

def Owners {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Prop :=
  ∀ (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
    FGl_PreparedAt.At c B s H e i p q data →
    Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
      (D2 c H) () e.pub e.proof e.saved.deref t →
    ∀ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
      Holds c.finish t.v2 t.p2 q p
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data


theorem weaken {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FGl_PreparedAt.Owners c B) : Owners c B := by
  intro s H e i p q data t atPrepared calls x
  have h := old s H e i p q data t atPrepared calls x
  exact ⟨h.1.pair,h.2.1,h.2.2.1⟩

#print axioms weaken
end AspisR1.FGm_Owners
end
