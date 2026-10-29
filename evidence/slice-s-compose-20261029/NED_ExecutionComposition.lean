import NED_CodecComposition
set_option autoImplicit false
noncomputable section
namespace NED_ExecutionComposition
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- The state and ordered effects are explicit. This is a transport carrier,
not a claim that Rust execution has been instantiated on this carrier. -/
structure Observation (R State Effect : Type) where
  result : R
  state : State
  effects : List Effect
  deriving DecidableEq

def validatorReference (s : NBN_StatementResult.Statement) :=
  NBN_ValidatorSummary.run atomic_statement.encode_digest_canonical
    (fun p => ok (NBP_PaymentModel.transfer_encoded p))
    (fun p => ok (NBP_PaymentModel.withdrawal_encoded p)) s

def encoderReference (s : NBN_StatementResult.Statement) :=
  NBN_StatementEncoderSummary.run atomic_statement.encode_digest_canonical
    (fun p => ok (NBP_PaymentModel.transfer_encoded p))
    (fun p => ok (NBP_PaymentModel.withdrawal_encoded p)) s

/-- Conditional transport of an already established SAME reference execution.
The physical equality is explicit; absent its concrete native certificate this
is not a CLOSED native root and must not be booked as one. -/
theorem validator_observation {State Effect : Type}
    (s : NBN_StatementResult.Statement) (st : State) (events : List Effect)
    (native : Observation (Result (core.result.Result Unit NBN_StatementResult.Error)) State Effect)
    (rootPhysicalInterpretation : native = ⟨validatorReference s,st,events⟩) :
    native = ⟨pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,st,events⟩ := by
  rw [rootPhysicalInterpretation]
  exact congrArg (fun r => Observation.mk r st events) (NED_CodecComposition.validator s)

theorem encoder_observation {State Effect : Type}
    (s : NBN_StatementResult.Statement) (st : State) (events : List Effect)
    (native : Observation NBN_StatementEncoderSummary.BytesResult State Effect)
    (rootPhysicalInterpretation : native = ⟨encoderReference s,st,events⟩) :
    native = ⟨NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),st,events⟩ := by
  rw [rootPhysicalInterpretation]
  exact congrArg (fun r => Observation.mk r st events) (NED_CodecComposition.encoder s)

#print axioms validator_observation
#print axioms encoder_observation
end NED_ExecutionComposition
