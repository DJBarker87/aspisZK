import FGl_PreparedAt
import F3V_RunEvidence
import FGl_FinishLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_Transport
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

def AcceptedOwners {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : Prop :=
  ∀ (s : Submission) (H : Bytes → State) (e : Evidence c B s H)
    (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs) (t : Cons_Native.Witness),
    FGl_PreparedAt.At c B s H e i p q data →
    Cons_Native.Calls (Op5T_Concrete.stage (AuS1_Install.base c.stageBase)) c.finish c.reserved c.query c.geometry
      (D2 c H) () e.pub e.proof e.saved.deref t →
    Port4D_FinishInstall.finish c.finish t.v2 t.p2
      {t.returned2 with weights:=t.back2 t.flushed2} none=ok (.Ok ()) →
    ∀ x : F3S_FinishWitness.Primitives c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2},
      FGl_FinishLeaves.Holds c.finish t.v2 t.p2 {t.returned2 with weights:=t.back2 t.flushed2} x q p
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) data

/-- No law at a single fixed H is promoted to all worlds. This transports a
source-derived law whose SAME accepted-run parameters are already arbitrary.
The arithmetic leaves inside AcceptedOwners are not proved by this theorem. -/
theorem generalise {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (source : AcceptedOwners c B) : FGl_PreparedAt.Owners c B := by
  intro s H e i p q data t atPrepared calls x
  have ⟨_,_,_,_,_,_,_,_,_,finishCall,_⟩ := calls
  exact source s H e i p q data t atPrepared calls finishCall x

/-- The acceptance guard adds no new premise: Calls already supplies it. -/
theorem same_domain {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    AcceptedOwners c B ↔ FGl_PreparedAt.Owners c B := by
  constructor
  · exact generalise c B
  · intro laws s H e i p q data t atPrepared calls _ x
    exact laws s H e i p q data t atPrepared calls x

#print axioms generalise
#print axioms same_domain
end AspisR1.FGl_Transport
end
