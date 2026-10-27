import RPt_FJp_GlobalOwners
import RPt_FIr_GlobalOwners2
import RPt_FJu_Remaining
import RPz8_F3V_Checkpoint
import RPt_FJp_Remaining
import RPz8_FGl_PreparedAt
import RPz7_SAG_NativeFull
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJu_GlobalOwners
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
      FJu_Remaining.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data

theorem weaken {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FJp_GlobalOwners.Owners c B) : Owners c B := by
  intro s H e i p q data t prepared calls shape x
  obtain ⟨pair,endpoint⟩ := old s H e i p q data t prepared calls shape x
  refine ⟨pair,?_⟩
  intro view claim polys opening claimRead polyRead
  exact (endpoint view claim polys opening claimRead polyRead).2.2

theorem complete {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (owners : Owners c B) : FJp_GlobalOwners.Owners c B := by
  intro s H e i p q data t prepared calls shape x
  obtain ⟨pair,endpoint⟩ := owners s H e i p q data t prepared calls shape x
  refine ⟨pair,?_⟩
  intro view claim polys opening claimRead polyRead
  have parser := prepared.2.2.1
  rw [prepared.2.1] at parser
  have first := FIr_PhysicalInitial.on_run (Op5T_Concrete.current c.currentBase)
    c.reserved c.query c.geometry c.boundaries c.std (D1 c H) ()
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved
    e.run p q _ parser view claim polys opening claimRead polyRead
  obtain ⟨out,v,output,viewRead,numeric,log,guard⟩ := prepared.2.2.2.2.2.2
  have sameView := Option.some.inj (viewRead.symm.trans opening)
  subst v
  have chain := FIr_PhysicalChain.on_run (Op5T_Concrete.current c.currentBase)
    c.reserved c.query c.geometry c.boundaries c.std (D1 c H) ()
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.pub e.proof 10#usize e.saved
    e.run p q _ parser view claim polys opening claimRead polyRead out output data numeric
    (fun j=>FIr_TranscriptRange.view H i.proof i.semantic.value p q view opening (15+j.val))
  exact ⟨first,chain,endpoint view claim polys opening claimRead polyRead⟩

#print axioms weaken
#print axioms complete
end AspisR1.FJu_GlobalOwners
end
