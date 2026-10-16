import ExtractedWithdrawalCallerSuccess
import ExtractedDecoderWithdrawalSuccess

/-! Fixed all-nine-field transport between the actual decoder extraction and
the standalone ASWP extraction. The original generated computations are related
without assuming validator or encoder agreement. Caller reachability, accounts,
and the separate semantic serializer remain outside this statement. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1TerminalDecoder.CallerBridge
abbrev Public := AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev CallerPublic := AspisR1WithdrawalCaller.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev DecoderError := AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev CallerError := AspisR1WithdrawalCaller.pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def toCaller (p : Public) : CallerPublic :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

def fromCaller (p : CallerPublic) : Public :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

theorem from_to (p : Public) : fromCaller (toCaller p) = p := by cases p; rfl
theorem to_from (p : CallerPublic) : toCaller (fromCaller p) = p := by cases p; rfl

def toError : DecoderError → CallerError
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

def mapOutcome {α : Type} : Result (core.result.Result α DecoderError) →
    Result (core.result.Result α CallerError)
  | .ok (.Ok a) => .ok (.Ok a)
  | .ok (.Err e) => .ok (.Err (toError e))
  | .fail e => .fail e
  | .div => .div

private theorem map_bind {α β : Type} (m : Result α)
    (k : α → Result (core.result.Result β DecoderError)) :
    mapOutcome (do let a ← m; k a) = (do let a ← m; mapOutcome (k a)) := by
  cases m <;> rfl

private theorem bind_congr {α β : Type} (m : Result α) (k l : α → Result β)
    (h : ∀ x, k x = l x) :
    (do let x ← m; k x) = (do let x ← m; l x) := by
  cases m with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

private theorem bind_pair_congr {α β γ : Type} (m : Result (α × β))
    (k l : α × β → Result γ) (h : ∀ a b, k (a, b) = l (a, b)) :
    (do let x ← m; k x) = (do let x ← m; l x) := by
  apply bind_congr
  intro x
  cases x with
  | mk a b => exact h a b

private theorem map_ite {α : Type} (p : Prop) [Decidable p]
    (x y : Result (core.result.Result α DecoderError)) :
    mapOutcome (if p then x else y) = if p then mapOutcome x else mapOutcome y := by
  split <;> rfl

private theorem map_ok {α : Type} (a : α) :
    mapOutcome (ok (.Ok a)) = ok (.Ok a) := rfl

private theorem map_err {α : Type} (e : DecoderError) :
    mapOutcome (ok (core.result.Result.Err (T := α) e)) = ok (.Err (toError e)) := rfl

def toCommon (p : AspisR1TerminalDecoder.pool_v1.payment_relation.CommonPublicV1) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.CommonPublicV1 :=
  { pool := p.pool, deployment_domain := p.deployment_domain,
    anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
    nullifier := p.nullifier, asset_id := p.asset_id }

theorem digest_eq (d : Array U32 8#usize) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.digest_is_canonical d =
      AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical d := by
  unfold AspisR1WithdrawalCaller.pool_v1.payment_relation.digest_is_canonical
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical AspisR1WithdrawalCaller.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem common_eq (p : AspisR1TerminalDecoder.pool_v1.payment_relation.CommonPublicV1) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common (toCommon p) =
      mapOutcome (AspisR1TerminalDecoder.pool_v1.payment_relation.validate_common p) := by
  simp only [AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common,
    AspisR1TerminalDecoder.pool_v1.payment_relation.validate_common, toCommon,
    AspisR1WithdrawalCaller.pool_v1.POOL_V1_LEAF_CAPACITY, AspisR1TerminalDecoder.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY,
    AspisR1WithdrawalCaller.pool_v1.POOL_V1_TREE_DEPTH, AspisR1TerminalDecoder.pool_v1.format.POOL_V1_TREE_DEPTH,
    AspisR1WithdrawalCaller.aspis_core.field.P, AspisR1TerminalDecoder.aspis_core.field.P, digest_eq, map_bind, map_ite,
    map_ok, map_err, toError]

theorem validator_eq (p : Public) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 (toCaller p) =
      mapOutcome (AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p) := by
  unfold AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
    AspisR1TerminalDecoder.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
    AspisR1WithdrawalCaller.pool_v1.payment_relation.withdrawal_common AspisR1TerminalDecoder.pool_v1.payment_relation.withdrawal_common
  simp only [toCaller, bind_tc_ok]
  let cp : AspisR1TerminalDecoder.pool_v1.payment_relation.CommonPublicV1 :=
    { pool := p.pool
      deployment_domain := p.deployment_domain
      anchor_sequence := p.anchor_sequence
      anchor_root := p.anchor_root
      nullifier := p.nullifier
      asset_id := p.asset_id }
  have hc := common_eq cp
  dsimp only [toCommon, cp] at hc
  rw [hc]
  cases h : AspisR1TerminalDecoder.pool_v1.payment_relation.validate_common
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
        AspisR1TerminalDecoder.spend.VALUE_LIMIT, AspisR1WithdrawalCaller.VALUE_LIMIT, digest_eq, map_bind, map_ite, toError]

theorem encode_digest_eq (d : Array U32 8#usize) :
    AspisR1WithdrawalCaller.encode_digest_canonical d =
      AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical d := by
  unfold AspisR1WithdrawalCaller.encode_digest_canonical
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
    AspisR1WithdrawalCaller.encode_digest_canonical_loop
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop
    AspisR1WithdrawalCaller.encode_digest_canonical_loop.body
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop.body
    AspisR1WithdrawalCaller.aspis_core.field.M31.to_le_bytes
    AspisR1TerminalDecoder.aspis_core.field.M31.to_le_bytes
  rfl

theorem encode_common_eq (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (p : pool_v1.payment_relation.CommonPublicV1) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_common out magic
      .Withdrawal (toCommon p) =
      pool_v1.payment_relation.encode_common out magic .Withdrawal p := by
  simp only [AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_common,
    pool_v1.payment_relation.encode_common, toCommon, encode_digest_eq,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION,
    AspisR1WithdrawalCaller.pool_v1.POOL_V1_DIGEST_ENCODING_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.POOL_OFFSET,
    pool_v1.payment_relation.POOL_OFFSET,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
    pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    pool_v1.payment_relation.ANCHOR_ROOT_OFFSET,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.NULLIFIER_OFFSET,
    pool_v1.payment_relation.NULLIFIER_OFFSET,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.ASSET_ID_OFFSET,
    pool_v1.payment_relation.ASSET_ID_OFFSET,
    AspisR1WithdrawalCaller.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
    AspisR1WithdrawalCaller.aspis_core.field.M31.to_le_bytes,
    aspis_core.field.M31.to_le_bytes]
  rfl

/-- Exact outcome and returned-byte agreement, including outer failure/divergence
and every mapped payment-format error. -/
theorem encoder_eq (p : Public) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
      (toCaller p) =
      mapOutcome (pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p) := by
  unfold AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
    pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
  rw [validator_eq]
  cases h : pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 p with
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
      simp only [map_ok, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
        AspisR1WithdrawalCaller.pool_v1.payment_relation.withdrawal_common,
        pool_v1.payment_relation.withdrawal_common, toCaller]
      let cp : pool_v1.payment_relation.CommonPublicV1 :=
        { pool := p.pool, deployment_domain := p.deployment_domain,
          anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
          nullifier := p.nullifier, asset_id := p.asset_id }
      have hc := encode_common_eq (Array.repeat 216#usize 0#u8)
        pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC cp
      dsimp only [toCommon, cp] at hc
      have hm : AspisR1WithdrawalCaller.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC =
          pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC := by
        unfold AspisR1WithdrawalCaller.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
          pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
        rfl
      rw [hm, hc]
      simp only [map_bind, encode_digest_eq,
        AspisR1WithdrawalCaller.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
        pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET,
        AspisR1WithdrawalCaller.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
        pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
        AspisR1WithdrawalCaller.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
        pool_v1.payment_relation.SECOND_OUTPUT_OFFSET]
      apply bind_congr
      intro output1
      apply bind_pair_congr
      intro s back
      simp only [uncurry_apply_pair, map_bind, map_ok]
      apply bind_congr
      intro amountBytes
      apply bind_congr
      intro amountSlice
      apply bind_congr
      intro copiedAmount
      apply bind_pair_congr
      intro s3 back1
      simp only [uncurry_apply_pair, map_bind, map_ok]
      apply bind_congr
      intro destinationSlice
      apply bind_congr
      intro copiedDestination
      apply bind_pair_congr
      intro s6 back2
      simp only [uncurry_apply_pair, map_bind, map_ok]

/-- The decoder extraction's own nested encoder success transports unchanged
bytes to the standalone actual encoder on the fixed public map. -/
theorem encoder_success (p : Public) (bytes : Array U8 216#usize)
    (h : pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (.Ok bytes)) :
    AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
      (toCaller p) = ok (.Ok bytes) := by
  rw [encoder_eq, h]
  rfl

theorem terminal_success_encoder
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (p : Public)
    (h : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      (.Withdrawal c p) = ok (.Ok ())) :
    ∃ bytes : Array U8 216#usize,
      AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
        (toCaller p) = ok (.Ok bytes) := by
  obtain ⟨bytes, hp⟩ := WithdrawalSuccess.terminal_encoder_success c p h
  exact ⟨bytes, encoder_success p bytes hp⟩

/-- The actual decoder fixes the withdrawal record before carrier transport. -/
theorem decoder_success_encoder
    (asf8 : Slice U8)
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) (p : Public)
    (h : pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      asf8 = ok (.Ok (.Withdrawal c p))) :
    ∃ bytes : Array U8 216#usize,
      AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
        (toCaller p) = ok (.Ok bytes) := by
  obtain ⟨bytes, hp⟩ := WithdrawalSuccess.decoder_encoder_success asf8 c p h
  exact ⟨bytes, encoder_success p bytes hp⟩

#print axioms from_to
#print axioms to_from
#print axioms digest_eq
#print axioms common_eq
#print axioms validator_eq
#print axioms encode_digest_eq
#print axioms encode_common_eq
#print axioms encoder_eq
#print axioms encoder_success
#print axioms terminal_success_encoder
#print axioms decoder_success_encoder
end AspisR1TerminalDecoder.CallerBridge
