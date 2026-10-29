import NED_ExecutionComposition
set_option autoImplicit false
noncomputable section
namespace NED_NativeRoots
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBN_StatementResult
open NED_ExecutionComposition
abbrev ValidatorResult := Result (core.result.Result Unit NBN_StatementResult.Error)
abbrev EncoderResult := NBN_StatementEncoderSummary.BytesResult

/-- Root interpreter supplied by physical execution. The fields identify the
TWO frozen source symbols; this record does not assert any execution equality. -/
structure FrozenRoots (State Effect : Type) where
  validate_pool_v1_pair_forest_terminal_statement_v1 : Statement → State → Observation ValidatorResult State Effect
  encode_pool_v1_pair_forest_terminal_statement_v1 : Statement → State → Observation EncoderResult State Effect
  ValidatorPhysicalInterpretation : Statement → State → Prop
  EncoderPhysicalInterpretation : Statement → State → Prop

def ValidatorPacketDomain (_s : Statement) : Prop := True
def EncoderPacketDomain (_s : Statement) : Prop := True

/-- EXPLICIT P6/D188 semantic-transport trust, owner amendment five option A.
These are source-CALLER/reference contracts, not cohort equalities. The three
lower codec laws remain arguments and are discharged below, rather than
silently bundled in PhysicalInterpretation. This record requires a concrete
accepted-native packet association; merely constructing a generic join does
not supply that association. No uninstantiated field is booked as CLOSED. -/
structure NativeContractSemanticTransport {State Effect : Type}
    (native : FrozenRoots State Effect) : Prop where
  validatorCaller : ∀ (enc : NBN_ValidatorSummary.Encode)
      (t : NBN_ValidatorSummary.Transfer → NBN_ValidatorSummary.PaymentResult)
      (w : NBN_ValidatorSummary.Withdrawal → NBN_ValidatorSummary.PaymentResult),
    NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc →
    NBN_ValidatorSummary.NBN_Dep_TransferEncode t →
    NBN_ValidatorSummary.NBN_Dep_WithdrawalEncode w →
    ∀ s st, ValidatorPacketDomain s → native.ValidatorPhysicalInterpretation s st →
      native.validate_pool_v1_pair_forest_terminal_statement_v1 s st =
        ⟨NBN_ValidatorSummary.run enc t w s,st,[]⟩
  encoderCaller : ∀ (enc : NBN_ValidatorSummary.Encode)
      (t : NBN_ValidatorSummary.Transfer → NBN_ValidatorSummary.PaymentResult)
      (w : NBN_ValidatorSummary.Withdrawal → NBN_ValidatorSummary.PaymentResult),
    NBN_DigestResultDependency.NBN_Dep_DigestEncodeRaw enc →
    NBN_ValidatorSummary.NBN_Dep_TransferEncode t →
    NBN_ValidatorSummary.NBN_Dep_WithdrawalEncode w →
    ∀ s st, EncoderPacketDomain s → native.EncoderPhysicalInterpretation s st →
      native.encode_pool_v1_pair_forest_terminal_statement_v1 s st =
        ⟨NBN_StatementEncoderSummary.run enc t w s,st,[]⟩

theorem validator_native_root {State Effect : Type} (native : FrozenRoots State Effect)
    (NativeContractSemanticTransport : NativeContractSemanticTransport native)
    (s : Statement) (st : State) (PacketDomain : ValidatorPacketDomain s)
    (PhysicalInterpretation : native.ValidatorPhysicalInterpretation s st) :
    native.validate_pool_v1_pair_forest_terminal_statement_v1 s st =
      ⟨pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,st,[]⟩ := by
  have caller := NativeContractSemanticTransport.validatorCaller
    atomic_statement.encode_digest_canonical
    (fun p => ok (NBP_PaymentModel.transfer_encoded p))
    (fun p => ok (NBP_PaymentModel.withdrawal_encoded p))
    NED_CodecComposition.digest_canonical NED_CodecComposition.transfer_law
    NED_CodecComposition.withdrawal_law s st PacketDomain PhysicalInterpretation
  rw [NED_CodecComposition.validator s] at caller
  exact caller

theorem encoder_native_root {State Effect : Type} (native : FrozenRoots State Effect)
    (NativeContractSemanticTransport : NativeContractSemanticTransport native)
    (s : Statement) (st : State) (PacketDomain : EncoderPacketDomain s)
    (PhysicalInterpretation : native.EncoderPhysicalInterpretation s st) :
    native.encode_pool_v1_pair_forest_terminal_statement_v1 s st =
      ⟨NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),st,[]⟩ := by
  have caller := NativeContractSemanticTransport.encoderCaller
    atomic_statement.encode_digest_canonical
    (fun p => ok (NBP_PaymentModel.transfer_encoded p))
    (fun p => ok (NBP_PaymentModel.withdrawal_encoded p))
    NED_CodecComposition.digest_raw NED_CodecComposition.transfer_law
    NED_CodecComposition.withdrawal_law s st PacketDomain PhysicalInterpretation
  rw [NED_CodecComposition.encoder s] at caller
  exact caller

#print axioms validator_native_root
#print axioms encoder_native_root
end NED_NativeRoots
