import SCB_PhysicalRun
import DrvC_SourceEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCB_SourceReplay
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortStoredAdmissionC4

/-- The chronological-log sub-obligation forced by literal L159. It makes
the additional replay visible without assuming any carried-data equality. -/
def ReplayLogLaw (rust : Verifier) (P : Prover) (runtime : Runtime) : Prop :=
  ∀ (H : Bytes → State) (run : RunView),
    (eval H runtime).2 = some run → run.2.2 = true →
      let v := eval H (originalWith rust (canon P))
      run.1 = v.1 ++ (eval H (rust v.2.1)).1

theorem log_of_binding (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Port1_StoredCarrier.Physical rust) (P : Prover) (runtime : Runtime)
    (binding : StoredCarrierBinding D rust P runtime) : ReplayLogLaw rust P runtime := by
  intro H run observed accepted
  have same := congrArg (fun v : RunView => v.1) (binding H run observed accepted)
  rw [SCB_Replay.annotated_eval D rust physical (canon P) H] at same
  exact same

/-- This property is derived directly for the literal installed source entry,
with no restrictions on its configuration or physical byte submissions. -/
theorem installed_physical {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    Port1_StoredCarrier.Physical (DrvC_SourceEntry.source c hashv) := by
  intro i j pub stored
  simp only [DrvC_SourceEntry.source,pub,stored]

/-- A literal installed-driver instance of the obstruction. The accepted and
nonempty observations are explicit; this theorem does not fabricate a source
fixture or assert every configuration accepts. -/
theorem installed_single_run {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (P : Port1_StoredCarrier.ByteProver)
    (H : Bytes → State)
    (accepted : (eval H (originalWith (DrvC_SourceEntry.source c hashv)
      (canon (Port1_StoredCarrier.lift P)))).2.2 = true)
    (nonempty : (eval H (DrvC_SourceEntry.source c hashv
      (eval H (canon (Port1_StoredCarrier.lift P))).2)).1 ≠ []) :
    ¬ StoredCarrierBinding D (DrvC_SourceEntry.source c hashv) (Port1_StoredCarrier.lift P)
      (SCB_PhysicalRun.runtime (DrvC_SourceEntry.source c hashv) (Port1_StoredCarrier.lift P)) :=
  SCB_PhysicalRun.not_binding D _ (installed_physical c hashv) _ H accepted nonempty

#print axioms log_of_binding
#print axioms installed_physical
#print axioms installed_single_run
end AspisR1.SCB_SourceReplay
end
