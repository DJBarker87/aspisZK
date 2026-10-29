import NED_ExecutionComposition
import NBN_EncoderObservation
set_option autoImplicit false
noncomputable section
namespace NED_TypedEncoderObservation
open Aeneas Aeneas.Std Result
open NED_ExecutionComposition
abbrev R := Result (core.result.Result (Array U8 1880#usize) NBN_StatementResult.Error)

def observe {State Effect : Type} (x : Observation R State Effect) :
    Observation NBN_StatementEncoderSummary.BytesResult State Effect :=
  ⟨NBN_StatementEncoderSummary.observe x.result,x.state,x.effects⟩

theorem injective {State Effect : Type} : Function.Injective (@observe State Effect) := by
  rintro ⟨r,st,es⟩ ⟨r',st',es'⟩ same
  have hr := congrArg Observation.result same
  have hs := congrArg Observation.state same
  have he := congrArg Observation.effects same
  have resultSame : r = r' := NBN_EncoderObservation.faithful hr
  cases resultSame
  cases hs
  cases he
  rfl

/-- Observed byte equality suffices ONLY with the typed 1880-byte Result
carrier and the proved injectivity. Rejected Results and fail/div are kept. -/
theorem result (native : R) (s : NBN_StatementResult.Statement)
    (sameReference : NBN_StatementEncoderSummary.observe native = encoderReference s) :
    native = AspisS6OuterNativeInstalled.encode s :=
  NBN_EncoderObservation.faithful (sameReference.trans (NED_CodecComposition.encoder s))

theorem state_effects {State Effect : Type} (native : Observation R State Effect)
    (s : NBN_StatementResult.Statement) (st : State) (events : List Effect)
    (sameReference : observe native = ⟨encoderReference s,st,events⟩) :
    native = ⟨AspisS6OuterNativeInstalled.encode s,st,events⟩ := by
  apply injective
  exact sameReference.trans (congrArg (fun r => Observation.mk r st events) (NED_CodecComposition.encoder s))

#print axioms injective
#print axioms result
#print axioms state_effects
end NED_TypedEncoderObservation
