import PublicExtractedRawBridge431
import WithdrawalValidationAmount431
import PublicRawAmountGuard

/-! Fixed maps between two separately extracted copies of the same Rust public
structure. All nine fields are copied in both directions. Helper success is an
explicit premise; no verifier caller-success or runtime refinement is asserted.
The raw projection is the already checked fieldwise serializer projection. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1

namespace AspisR1PublicSerializer.WithdrawalCarrier431

abbrev SerializerPublic := Whole431.Withdrawal
abbrev ValidatorPublic := AspisR1WithdrawalValidation.Amount431.Public

def toValidator (p : SerializerPublic) : ValidatorPublic :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

def fromValidator (p : ValidatorPublic) : SerializerPublic :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

theorem from_to (p : SerializerPublic) : fromValidator (toValidator p) = p := by
  cases p
  rfl

theorem to_from (p : ValidatorPublic) : toValidator (fromValidator p) = p := by
  cases p
  rfl

/-- Metadata omitted by the small public-byte transcript is still copied into
the validator carrier; its caller/account binding remains a separate question. -/
theorem toValidator_fields (p : SerializerPublic) :
    (toValidator p).pool = p.pool ∧
    (toValidator p).deployment_domain = p.deployment_domain ∧
    (toValidator p).anchor_sequence = p.anchor_sequence ∧
    (toValidator p).anchor_root = p.anchor_root ∧
    (toValidator p).nullifier = p.nullifier ∧
    (toValidator p).asset_id = p.asset_id ∧
    (toValidator p).amount = p.amount ∧
    (toValidator p).destination_token_account = p.destination_token_account ∧
    (toValidator p).change_commitment = p.change_commitment :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- This predicate names only the actual extracted payment-helper computation.
It does not stand for success of a verifier, decoder, or on-chain caller. -/
def HelperValidated (p : SerializerPublic) : Prop :=
  AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
    (toValidator p) = ok (.Ok ())

theorem helper_success_amount_guard (p : SerializerPublic) (h : HelperValidated p) :
    0 < p.amount.val ∧ p.amount.val < 2 ^ 30 := by
  exact AspisR1WithdrawalValidation.Amount431.success_amount_guard (toValidator p) h

/-- The transition is unchanged and arbitrary; this theorem imposes no false
validation claim on its live snapshot or candidate afterstate. -/
theorem helper_success_raw_amount_guard (p : SerializerPublic) (t : Whole431.Transition)
    (h : HelperValidated p) :
    PublicRawAmountGuard.PaymentAmountGuard
      (RawBridge431.project (.Withdrawal p t)) := by
  exact helper_success_amount_guard p h

theorem helper_success_raw_nonzero (p : SerializerPublic) (t : Whole431.Transition)
    (h : HelperValidated p) :
    PublicRawAmountGuard.NonzeroWithdrawal
      (RawBridge431.project (.Withdrawal p t)) := by
  exact PublicRawAmountGuard.nonzero_of_payment_guard _
    (helper_success_raw_amount_guard p t h)

/-- Compose two explicitly separate extracted successes on the same fixed input.
The output bytes and input projection are inherited unchanged from RawBridge431. -/
theorem validated_source_success (p : SerializerPublic) (t : Whole431.Transition)
    (out : FieldsRefinement431.ByteVec) (hv : HelperValidated p)
    (hs : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal p t) = ok (.Ok out)) :
    PublicRawCore.serialize (RawBridge431.project (.Withdrawal p t)) =
        some (out.val.map RawBridge431.rawByte) ∧
      PublicRawAmountGuard.PaymentAmountGuard (RawBridge431.project (.Withdrawal p t)) ∧
      PublicRawAmountGuard.NonzeroWithdrawal (RawBridge431.project (.Withdrawal p t)) := by
  exact ⟨RawBridge431.source_success_raw _ out hs,
    helper_success_raw_amount_guard p t hv, helper_success_raw_nonzero p t hv⟩

#print axioms from_to
#print axioms to_from
#print axioms toValidator_fields
#print axioms helper_success_amount_guard
#print axioms helper_success_raw_amount_guard
#print axioms helper_success_raw_nonzero
#print axioms validated_source_success
end AspisR1PublicSerializer.WithdrawalCarrier431
