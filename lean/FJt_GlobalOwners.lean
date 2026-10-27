import FJt_Remaining
import FJt_GlobalTerminal
import FGl_PreparedAt
import SAG_NativeFull
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_GlobalOwners
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Five retained source-global families, conditioned on the actual source
view reads. Shape is derived by the source consumer, not a new input law. -/
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
      FJt_Remaining.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data

theorem complete {C : Type} (m : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (owners : Owners (FJt_GlobalTerminal.configuration m err r) B) :
    FIp_GlobalOwners.Owners (FJt_GlobalTerminal.configuration m err r) B := by
  intro s H e i p q data t prepared calls shape x
  obtain ⟨pair,matching,front⟩:=owners s H e i p q data t prepared calls shape x
  have terminal:=FJt_GlobalTerminal.value m err r B s H e i p q data prepared
  refine ⟨pair,matching,?_⟩
  intro view claim polys opening claimRead polyRead
  have first:=front view claim polys opening claimRead polyRead
  exact ⟨first.1,first.2,terminal view claim polys opening claimRead polyRead⟩

 theorem project {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (owners : FIp_GlobalOwners.Owners c B) : Owners c B := by
  intro s H e i p q data t prepared calls shape x
  exact FJt_Remaining.project _ _ _ _ x q p _ data (owners s H e i p q data t prepared calls shape x)
#print axioms complete
#print axioms project
end AspisR1.FJt_GlobalOwners
end
