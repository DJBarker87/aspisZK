import ExtractedWithdrawalCallerSuccess
import WithdrawalCarrierBridge431

/-! Fixed all-field carrier and actual validator agreement across the two exact
extractions. The Caller Types import uses the separately audited naming-only
Error discriminant adapter. No verifier or terminal reachability is assumed or
proved here; the premise is success of the actual extracted ASWP encoder. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1WithdrawalCaller.Carrier
abbrev Public := AspisR1WithdrawalCaller.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev ValidationPublic := AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev CallerError := AspisR1WithdrawalCaller.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev ValidationError := AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def toValidator (p : Public) : ValidationPublic :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

def fromValidator (p : ValidationPublic) : Public :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

theorem from_to (p : Public) : fromValidator (toValidator p) = p := by cases p; rfl
theorem to_from (p : ValidationPublic) : toValidator (fromValidator p) = p := by cases p; rfl

def toSerializer (p : Public) : AspisR1PublicSerializer.WithdrawalCarrier431.SerializerPublic := AspisR1PublicSerializer.WithdrawalCarrier431.fromValidator (toValidator p)

theorem serializer_validator (p : Public) : AspisR1PublicSerializer.WithdrawalCarrier431.toValidator (toSerializer p) = toValidator p :=
  AspisR1PublicSerializer.WithdrawalCarrier431.to_from _

def toError : CallerError → ValidationError
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongTransitionKind => .WrongTransitionKind
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidAnchorSequence => .InvalidAnchorSequence
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .NonCanonicalAssetId => .NonCanonicalAssetId
  | .InvalidWithdrawalAmount => .InvalidWithdrawalAmount
  | .InvalidDestination => .InvalidDestination
  | .InvalidEnvelope => .InvalidEnvelope
  | .EnvelopeMismatch => .EnvelopeMismatch

def mapOutcome {α : Type} : Result (core.result.Result α CallerError) →
    Result (core.result.Result α ValidationError)
  | .ok (.Ok a) => .ok (.Ok a)
  | .ok (.Err e) => .ok (.Err (toError e))
  | .fail e => .fail e
  | .div => .div

private theorem map_bind {α β : Type} (m : Result α)
    (k : α → Result (core.result.Result β CallerError)) :
    mapOutcome (do let a ← m; k a) = (do let a ← m; mapOutcome (k a)) := by
  cases m <;> rfl

private theorem map_ite {α : Type} (p : Prop) [Decidable p]
    (x y : Result (core.result.Result α CallerError)) :
    mapOutcome (if p then x else y) = if p then mapOutcome x else mapOutcome y := by
  split <;> rfl

private theorem map_ok {α : Type} (a : α) :
    mapOutcome (ok (.Ok a)) = ok (.Ok a) := rfl

private theorem map_err {α : Type} (e : CallerError) :
    mapOutcome (ok (core.result.Result.Err (T := α) e)) = ok (.Err (toError e)) := rfl

def toCommon (p : AspisR1WithdrawalCaller.pool_v1.payment_relation.CommonPublicV1) :
    AspisR1WithdrawalValidation.pool_v1.payment_relation.CommonPublicV1 :=
  { pool := p.pool, deployment_domain := p.deployment_domain,
    anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
    nullifier := p.nullifier, asset_id := p.asset_id }

theorem digest_eq (d : Array U32 8#usize) :
    AspisR1WithdrawalValidation.pool_v1.payment_relation.digest_is_canonical d =
      AspisR1WithdrawalCaller.pool_v1.payment_relation.digest_is_canonical d := by
  unfold AspisR1WithdrawalValidation.pool_v1.payment_relation.digest_is_canonical
    AspisR1WithdrawalCaller.pool_v1.payment_relation.digest_is_canonical AspisR1WithdrawalValidation.aspis_core.field.P AspisR1WithdrawalCaller.aspis_core.field.P
  rfl

theorem common_eq (p : AspisR1WithdrawalCaller.pool_v1.payment_relation.CommonPublicV1) :
    AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_common (toCommon p) =
      mapOutcome (AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common p) := by
  simp only [AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_common,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common, toCommon,
    AspisR1WithdrawalValidation.pool_v1.POOL_V1_LEAF_CAPACITY, AspisR1WithdrawalCaller.pool_v1.POOL_V1_LEAF_CAPACITY,
    AspisR1WithdrawalValidation.pool_v1.POOL_V1_TREE_DEPTH, AspisR1WithdrawalCaller.pool_v1.POOL_V1_TREE_DEPTH,
    AspisR1WithdrawalValidation.aspis_core.field.P, AspisR1WithdrawalCaller.aspis_core.field.P, digest_eq, map_bind, map_ite,
    map_ok, map_err, toError]

theorem validator_eq (p : Public) :
    AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 (toValidator p) =
      mapOutcome (AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p) := by
  unfold AspisR1WithdrawalValidation.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
    AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
    AspisR1WithdrawalValidation.pool_v1.payment_relation.withdrawal_common AspisR1WithdrawalCaller.pool_v1.payment_relation.withdrawal_common
  simp only [toValidator, bind_tc_ok]
  let cp : AspisR1WithdrawalCaller.pool_v1.payment_relation.CommonPublicV1 :=
    { pool := p.pool
      deployment_domain := p.deployment_domain
      anchor_sequence := p.anchor_sequence
      anchor_root := p.anchor_root
      nullifier := p.nullifier
      asset_id := p.asset_id }
  have hc := common_eq cp
  dsimp only [toCommon, cp] at hc
  rw [hc]
  cases h : AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common
      { pool := p.pool
        deployment_domain := p.deployment_domain
        anchor_sequence := p.anchor_sequence
        anchor_root := p.anchor_root
        nullifier := p.nullifier
        asset_id := p.asset_id } with
  | fail e => rfl
  | div => rfl
  | ok x =>
    cases x with
    | Err e =>
      simp only [mapOutcome, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
    | Ok u =>
      cases u
      simp only [map_ok, map_err, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
        AspisR1WithdrawalCaller.VALUE_LIMIT, AspisR1WithdrawalValidation.VALUE_LIMIT, digest_eq, map_bind, map_ite, toError]

theorem encoder_success_helper (p : Public) (bytes : Array U8 216#usize)
    (h : AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (.Ok bytes)) :
    AspisR1PublicSerializer.WithdrawalCarrier431.HelperValidated (toSerializer p) := by
  unfold AspisR1PublicSerializer.WithdrawalCarrier431.HelperValidated
  rw [serializer_validator, validator_eq, AspisR1WithdrawalCaller.CallerSuccess.encoder_success_validator p bytes h]
  rfl

theorem encoder_success_amount_guard (p : Public) (bytes : Array U8 216#usize)
    (h : AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (.Ok bytes)) :
    0 < p.amount.val ∧ p.amount.val < 2 ^ 30 := by
  exact AspisR1PublicSerializer.WithdrawalCarrier431.helper_success_amount_guard (toSerializer p) (encoder_success_helper p bytes h)

#print axioms from_to
#print axioms to_from
#print axioms serializer_validator
#print axioms digest_eq
#print axioms common_eq
#print axioms validator_eq
#print axioms encoder_success_helper
#print axioms encoder_success_amount_guard
end AspisR1WithdrawalCaller.Carrier
