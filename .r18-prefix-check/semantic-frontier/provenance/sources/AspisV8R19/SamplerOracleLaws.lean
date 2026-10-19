import AspisV8R19.QM31SamplerProgram
import AspisV8R19.Q22SamplerProgram

/-! Exact memoized-oracle laws for the compiled source-shaped samplers.
This does not assert independent field challenges conditional on later roots,
nor replace SHA by a uniform oracle as a computational-security theorem. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerOracleLaws
open DuplexFrames SourceDuplexStep SourceOraclePrograms
open MemoizedProgramLaw OracleFiniteSupport OracleResampling

def CorrectLaw {O : Type} (p : Program Bytes State O) (run : (Bytes → State) → View Bytes State O) : Prop :=
  ∀ (fallback : State) (observe : View Bytes State O → ℚ),
    mean (fun H : {i // i ∈ support p} → State =>
      observe (run (extend (support p) H fallback))) =
      lazyMean p (fun _ => none) observe

theorem law_of_exact {O : Type} (p : Program Bytes State O)
    (run : (Bytes → State) → View Bytes State O) (exactRun : ∀ H, eval H p = run H) :
    CorrectLaw p run := by
  intro fallback observe
  have h := byte_program_law p fallback observe
  simpa only [exactRun] using h

theorem qm31_law (s : State) :
    CorrectLaw (QM31SamplerProgram.challengeProgram s) (fun H => QM31SamplerProgram.challengeRun H s) :=
  law_of_exact (QM31SamplerProgram.challengeProgram s) (fun H => QM31SamplerProgram.challengeRun H s)
    (fun H => QM31SamplerProgram.challenge_exact H s)

theorem q22_law (s : State) :
    CorrectLaw (Q22SamplerProgram.challengeProgram s) (fun H => Q22SamplerProgram.challengeRun H s) :=
  law_of_exact (Q22SamplerProgram.challengeProgram s) (fun H => Q22SamplerProgram.challengeRun H s)
    (fun H => Q22SamplerProgram.challenge_exact H s)

#print axioms law_of_exact
#print axioms qm31_law
#print axioms q22_law
end AspisV8R19.SamplerOracleLaws
