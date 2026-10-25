import Hiq_StoredMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_StoredTransport
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortStoredAdmissionC4
open RawRecordedOracleExtractionMassBin

/-- Probability transport may charge a same-world bad event. The all-H whole
run equality outside that event remains EXPLICIT and is not proved here. -/
theorem pointwise {A : Type} (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) (source : Program Bytes State A) (bad : View Bytes State A → Prop)
    (binding : ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
      run = eval H (annotatedWith D rust (canon P)) ∨ bad (eval H source))
    (H : Bytes → State) :
    runtimeMass (eval H runtime) ≤
      failureMass (view (eval H (annotatedWith D rust (canon P)))) + indicator (bad (eval H source)) := by
  classical
  have nonneg := failure_nonnegative (view (eval H (annotatedWith D rust (canon P))))
  have badNonneg := indicator_nonneg (bad (eval H source))
  cases actual : (eval H runtime).2 with
  | none =>
    simp only [runtimeMass,actual]
    exact add_nonneg nonneg badNonneg
  | some run =>
    change failureMass (view run) ≤ _
    by_cases accepted : run.2.2 = true
    · rcases binding H run actual accepted with same | hit
      · rw [same]
        exact le_add_of_nonneg_right badNonneg
      · have one : indicator (bad (eval H source)) = 1 := by simp [indicator,hit]
        rw [one]
        exact (Hiq_StoredMass.failure_le_one (view run)).trans (by linarith)
    · rw [Hiq_StoredMass.rejected_zero run accepted]
      exact add_nonneg nonneg badNonneg

theorem transport {A : Type} (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) (source : Program Bytes State A) (bad : View Bytes State A → Prop)
    (binding : ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
      run = eval H (annotatedWith D rust (canon P)) ∨ bad (eval H source)) :
    deployedFailure runtime ≤
      lazyMean (annotatedWith D rust (canon P)) emptyTable (fun v => failureMass (view v)) +
      lazyMean source emptyTable (fun v => indicator (bad v)) :=
  Hiq_MeanSum.le_sum runtime (annotatedWith D rust (canon P)) source runtimeMass
    (fun v => failureMass (view v)) (fun v => indicator (bad v))
    (pointwise D rust P runtime source bad binding)

#print axioms pointwise
#print axioms transport
end AspisR1.Hiq_StoredTransport
end
