import OraclePortStoredProbabilityC7

/-! Explicit unproved execution and runtime joins for the draft headline.
Full stored inputs survive in Runtime, through the probability experiment. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRuntimeBindingC7
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortStoredConsumerC7
open RawRecordedOracleExtractionMassBin

abbrev Verifier := Input → Program Bytes State Bool
abbrev Runtime := Program Bytes State (Option RunView)

def originalWith (rust : Verifier) (P : Prover) : Program Bytes State (Input × Bool) :=
  bind P fun i => bind (rust i) fun ok => .done (i,ok)

def annotatedWith (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover) :=
  originalWith rust (bind (OracleProgramRecording.record (originalWith rust P)) fun v =>
    .done (enrich (build D (view v)) v.2.1))

/-- Complete oracle-program equality, including every read, rejection and
returned Bool. This is the frozen Rust/source join, still a hypothesis. -/
def ExecutionJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop :=
  ∀ i : Input, rust i = verifier D dV i

theorem annotatedWith_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (join : ExecutionJoin D rust) (P : Prover) :
    annotatedWith D rust P = annotated D dV P := by
  have hr : rust = verifier D dV := funext join
  rw [hr]
  rfl

/-- Runtime must bind the whole stored carrier and trace on every accepted
resumed run, in the same oracle world; this is stronger than a mass premise. -/
def StoredCarrierBinding (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) : Prop :=
  ∀ H : Bytes → State, ∀ run : RunView,
    (eval H runtime).2 = some run → run.2.2 = true →
      run = eval H (annotatedWith D rust (canon P))

def runtimeMass (v : View Bytes State (Option RunView)) : ℚ :=
  match v.2 with
  | none => 0
  | some run => failureMass (view run)

def deployedFailure (runtime : Runtime) : ℚ := lazyMean runtime emptyTable runtimeMass

theorem failure_nonnegative (run : RawCutProverCompiler.RunView) : 0 ≤ failureMass run := by
  unfold failureMass
  have h := mean_mono (fun coins : GSConcreteByteDecoderBank.RawCoins =>
    indicator_nonneg (run.2.2 = true ∧ RawRecordedPublicSpendExtractorBin.extract run coins = none))
  simpa only [mean_const] using h

theorem transport (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : Prover)
    (runtime : Runtime) (join : ExecutionJoin D rust)
    (binding : StoredCarrierBinding D rust P runtime) :
    deployedFailure runtime ≤ lazyMean (projected D P) emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none => exact failure_nonnegative _
  | some run =>
      change failureMass (view run) ≤ failureMass (eval H (projected D P))
      by_cases accepted : run.2.2 = true
      · have same := binding H run hr accepted
        rw [annotatedWith_eq D rust join] at same
        rw [same,projected_eval]
      · have zero : failureMass (view run) = 0 := by
          unfold failureMass
          simp only [view] at *
          simp [accepted,indicator,mean_const]
        rw [zero]
        exact failure_nonnegative _

#print axioms annotatedWith_eq
#print axioms failure_nonnegative
#print axioms transport
end AspisR1.OraclePortRuntimeBindingC7
end
