import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.SamplerRawStateRepresentation

/-! Reparameterisation of an already-independent answer interpreter.

This is a finite representation transport only.  It does not assert freshness,
oracle independence, or any source/callback correspondence.
-/
set_option autoImplicit false
namespace AspisV8R19.IndependentAnswerTransport

open MemoizedProgramLaw OracleProgramOps OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.SamplerRawStateRepresentation
open DuplexFrames SourceDuplexStep

variable {I A B O : Type}

def recodeAnswers (e : A ≃ B) : Program I A O → Program I B O
  | .done o => .done o
  | .ask i next => .ask i (fun b => recodeAnswers e (next (e.symm b)))

def decodeView (e : A ≃ B) : View I B O → View I A O
  | (trace,outcome) =>
      (trace.map (fun p => (p.1,e.symm p.2)), outcome)

theorem independentMean_recodeAnswers [Fintype A] [Fintype B]
    (e : A ≃ B) (p : Program I A O) (observe : View I A O → ℚ) :
    independentMean (recodeAnswers e p) (observe ∘ decodeView e) =
      independentMean p observe := by
  induction p generalizing observe with
  | done o => rfl
  | ask i next ih =>
      simp only [recodeAnswers, independentMean, Function.comp_apply]
      rw [← mean_equiv e.symm]
      apply mean_congr
      intro a
      simpa [decodeView, Function.comp_def] using ih (e.symm a) (fun r =>
        observe ((i,e.symm a)::r.1,r.2))

theorem independentMean_stateRaw_transport [Fintype (Fin 32 → Byte)]
    (p : Program I (Fin 32 → Byte) O)
    (observe : View I (Fin 32 → Byte) O → ℚ) :
    independentMean
        (recodeAnswers stateRawEquiv p)
        (observe ∘ decodeView stateRawEquiv) =
      independentMean p observe :=
  independentMean_recodeAnswers stateRawEquiv p observe

#print axioms independentMean_recodeAnswers
#print axioms independentMean_stateRaw_transport
end AspisV8R19.IndependentAnswerTransport
