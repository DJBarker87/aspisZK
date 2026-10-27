import FJs_GlobalPair
import FIp_Remaining
import FGl_PreparedAt
import SAG_NativeFull
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_GlobalOwners
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
      (∀ j,MatchingSupport.match0 data.data (q j)) ∧
      R3SemanticRemainingJoins.EquationEndpoint data.decoded (OraclePortStoredDecisionDraftC4.typedRows p q
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)) data.data

theorem complete {C : Type} (err : C) (base : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (remaining : Owners (FIp_Install.configuration err base r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r).boundaries) :
    FIp_GlobalOwners.Owners (FIp_Install.configuration err base r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r).boundaries := by
  intro s H e i p q data t atPrepared calls shape x
  exact ⟨FJs_GlobalPair.law err base r s H e i p q data t atPrepared calls shape,
    remaining s H e i p q data t atPrepared calls shape x⟩

theorem of_original {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (old : FIp_GlobalOwners.Owners c B) : Owners c B := by
  intro s H e i p q data t atPrepared calls shape x
  exact (old s H e i p q data t atPrepared calls shape x).2

#print axioms complete
#print axioms of_original
end AspisR1.FJs_GlobalOwners
end
