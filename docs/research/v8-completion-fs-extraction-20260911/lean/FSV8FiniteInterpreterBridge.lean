import FSV8V7FiniteUniformBridge

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8FiniteInterpreterBridge
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSV8FreshTapeBudget FSV8V7FiniteTapeEmbedding
open AspisK1.V7Tag73TranscriptSchedule AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV8PostOODGammaScript.Point

noncomputable section

def extendFiniteTape {steps : Nat} (finite : Fin steps → Block)
    (fallback : Block) : Tape :=
  fun j => if h : j < steps then finite ⟨j, h⟩ else fallback

def finiteInterpreter {n m steps : Nat}
    (finite : Fin steps → Block) (fallback : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) :=
  run (extendFiniteTape finite fallback)
    (sourceThenGammaScript firstWork secondWork body digest)
    (FSFirstFresh.empty : Oracle)

theorem finiteInterpreter_agrees_with_nat_tape
    {n m steps : Nat} (finite : Fin steps → Block) (fallback : Block)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape)
    (same : ∀ (j : Nat) (hj : j < steps), tape j = finite ⟨j, hj⟩)
    (budget : sourceThenGammaBudget n m ≤ steps) :
    finiteInterpreter finite fallback firstWork secondWork body digest =
      run tape (sourceThenGammaScript firstWork secondWork body digest)
        (FSFirstFresh.empty : Oracle) := by
  apply run_tape_congr
  intro j hj hbound
  have jltBudget : j < sourceThenGammaBudget n m := by
    simpa [sourceThenGammaBudget, FSFirstFresh.empty] using hbound
  have jltSteps : j < steps := lt_of_lt_of_le jltBudget budget
  simp only [extendFiniteTape]
  rw [dif_pos jltSteps]
  exact (same j jltSteps).symm

/-- The finite-input interpreter is the deterministic map to which a later
    finite-tape law may be applied. This declaration intentionally stops before
    event coupling, acceptance, or adversarial source correspondence. -/
def finiteInterpreterMap {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) :
    (Fin steps → Block) →
      (Option (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
        (OODResult × Gamma) × Block) × Oracle) :=
  fun finite => finiteInterpreter finite fallback firstWork secondWork body digest

/-- The explicit finite-tape experiment.  Calling this the distribution of
    the deployed random oracle still requires the missing source/first-exposure
    coupling; here it is only the pushforward of the stated uniform tape. -/
noncomputable def finiteInterpreterDistribution {n m steps : Nat}
    (fallback : Block) (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) :
    PMF (Option
      (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
        (OODResult × Gamma) × Block) × Oracle) :=
  (PMF.uniformOfFintype (Fin steps → Block)).map
    (finiteInterpreterMap fallback firstWork secondWork body digest)

#print axioms finiteInterpreter_agrees_with_nat_tape
end
end AspisV8Completion.FSV8FiniteInterpreterBridge
