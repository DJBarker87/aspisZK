import ExtractedAdapterTransferBindings
import ExtractedPublicCheckedBridge432
import R1SemanticPublicWireRoundTrip

/-! R9 obligations over the actual serializer and reconstruction. Named Props
are obligations, not axioms or claims of caller reachability. Stage 2 does not
call public_bytes: Stage2SameBytes specifies the equality its reconstructed
statement must satisfy against the stage-1 bytes. No decoder cone is imported. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1PublicSerializer
namespace AspisR1AdapterReconstruct.StageBinding
open aspis_statement.pool_v1.pair_forest_terminal
open aspis_statement.pool_v1.pair_terminal
open r1_pool_adapter

/-- Fixed nominal transport, retaining every snapshot and candidate field. -/
def toTransition (t : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    Whole431.Transition :=
  { live_snapshot :=
      { pool := t.live_snapshot.pool
        deployment_domain := t.live_snapshot.deployment_domain
        sequence := t.live_snapshot.sequence
        next_pair_index := t.live_snapshot.next_pair_index
        current_root := t.live_snapshot.current_root
        frontier := t.live_snapshot.frontier }
    candidate_afterstate :=
      { next_pair_index := t.candidate_afterstate.next_pair_index
        next_root := t.candidate_afterstate.next_root
        next_frontier := t.candidate_afterstate.next_frontier } }

def toTransfer (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    Whole431.Transfer :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    recipient_commitment := p.recipient_commitment
    change_commitment := p.change_commitment }

def toWithdrawal (p : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    Whole431.Withdrawal :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

/-- Fixed field copy matching semantic_public's variant/transition selector.
This is a nominal map, not an execution theorem about the stage-1 caller. -/
def toSerializer : PoolV1PairForestTerminalStatementV1 → Whole431.Public
  | .PrivateTransfer c p => .Transfer (toTransfer p) (toTransition c.lane_transition)
  | .Withdrawal c p => .Withdrawal (toWithdrawal p) (toTransition c.lane_transition)

/-- Exact hs premise on the public argument reached at stage 1 and its bytes.
Proving that an accepted transaction reaches this success remains open. -/
def SerializerWitness (stage1 : Whole431.Public) (bytes : FieldsRefinement431.ByteVec) : Prop :=
  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes stage1 = ok (.Ok bytes)

/-- hbind in fixed computed-public form; no public is chosen from bytes. -/
def SuppliedPublicBinding (stage1 : Whole431.Public)
    (supplied : R0P.Public SemanticPublicWire.M31) : Prop :=
  (PublicSourceRaw.toWire (ExtractedPublicCheckedBridge432.projectRaw stage1)).map
    SemanticPublicWire.toPublic = some supplied

/-- An additional guard for withdrawal parsing; transfer discharges it below. -/
def PaymentGuard (stage1 : Whole431.Public) : Prop :=
  PublicRawAmountGuard.PaymentAmountGuard (RawBridge431.project stage1)

/-- Equality of the actual stage-1 serializer argument to the fixed projection
of stage-2 reconstruction. It does not infer omitted account metadata. -/
def SameSemanticPublic (stage1 : Whole431.Public)
    (stage2 : PoolV1PairForestTerminalStatementV1) : Prop :=
  stage1 = toSerializer stage2

/-- Stage-2 reconstruction must return a statement whose semantic serialization
equals the stage-1 bytes. This specifies an equation, not a stage-2 call. -/
def Stage2SameBytes (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (stage1bytes : FieldsRefinement431.ByteVec) : Prop :=
  ∃ out, reconstruct_asq8_statement request a candidate = ok (.Ok out) ∧
    SerializerWitness (toSerializer out) stage1bytes

theorem transfer_payment_guard (c : PoolV1PairForestTerminalCommonV1)
    (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    PaymentGuard (toSerializer (.PrivateTransfer c p)) := by trivial

theorem hbind_of_wire (s : Whole431.Public) (wire : SemanticPublicWire.Wire)
    (supplied : R0P.Public SemanticPublicWire.M31)
    (hw : PublicSourceRaw.toWire (ExtractedPublicCheckedBridge432.projectRaw s) = some wire)
    (hbind : supplied = SemanticPublicWire.toPublic wire) :
    SuppliedPublicBinding s supplied := by
  simp only [SuppliedPublicBinding, hw, Option.map_some, hbind]

/-- Complete the parser consequence from the retained encode-to-wire law.
The local R1PublicCodecAgreement cache contains that law, but not the later
repository parsePublic_of_decode declaration. No generated module is changed. -/
private theorem parsePublic_of_wire_decode (bytes : PublicByteCodec.Bytes)
    (wire : SemanticPublicWire.Wire)
    (hd : PublicByteCodec.decode bytes = some (SemanticPublicWire.toPublic wire)) :
    SemanticPublicWire.parsePublic bytes = some (SemanticPublicWire.toPublic wire) := by
  obtain ⟨he, hc⟩ := (PublicByteCodec.decode_eq_some_iff _ _).mp hd
  have hb : SemanticPublicWire.encode wire = bytes :=
    Option.some.inj ((PublicCodecAgreement.encode_toPublic_eq_wire_encode wire).symm.trans he)
  have hwc : PublicOptionShape.canonical (SemanticPublicWire.toPublic wire) :=
    by simpa only [PublicOptionShape.check_eq_true_iff] using hc
  rw [← hb]
  exact SemanticPublicWireRoundTrip.parsePublic_encode wire hwc

/-- Serializer success and the payment guard identify the fixed computed
public. The separately supplied public still requires hbind. -/
theorem serializer_supplied_public (s : Whole431.Public)
    (bytes : FieldsRefinement431.ByteVec) (supplied : R0P.Public SemanticPublicWire.M31)
    (hs : SerializerWitness s bytes) (hguard : PaymentGuard s)
    (hbind : SuppliedPublicBinding s supplied) :
    SemanticPublicWire.parsePublic (bytes.val.map RawBridge431.rawByte) = some supplied := by
  have hraw := RawBridge431.extracted_refines_core s (bytes.val.map RawBridge431.rawByte)
    ⟨bytes, hs, rfl⟩
  obtain ⟨wire, hw, hd⟩ := PublicRawAmountGuardAgreement.decoded_of_guarded_core_success
    (RawBridge431.project s) (bytes.val.map RawBridge431.rawByte) hraw hguard
  have hp := parsePublic_of_wire_decode _ _ hd
  change (PublicSourceRaw.toWire (ExtractedPublicCheckedBridge432.projectRaw s)).map
    SemanticPublicWire.toPublic = some supplied at hbind
  change PublicSourceRaw.toWire (ExtractedPublicCheckedBridge432.projectRaw s) = some wire at hw
  rw [hw] at hbind
  exact hp.trans hbind

/-- Determinism gives byte equality once the same semantic argument is known. -/
theorem same_public_unique_bytes (s : Whole431.Public)
    (out : PoolV1PairForestTerminalStatementV1)
    (b1 b2 : FieldsRefinement431.ByteVec)
    (heq : SameSemanticPublic s out)
    (hs1 : SerializerWitness s b1) (hs2 : SerializerWitness (toSerializer out) b2) :
    b1 = b2 := by
  change s = toSerializer out at heq
  rw [heq] at hs1
  exact core.result.Result.Ok.inj (Result.ok.inj (hs1.symm.trans hs2))

/-- Conditional R9 composition for both variants. hs, hbind and heq are named
obligations, never inferred from reconstruction success or byte injectivity. -/
theorem r9_of_same_public
    (s : Whole431.Public) (bytes : FieldsRefinement431.ByteVec)
    (supplied : R0P.Public SemanticPublicWire.M31)
    (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1)
    (hs : SerializerWitness s bytes) (hguard : PaymentGuard s)
    (hbind : SuppliedPublicBinding s supplied)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out))
    (heq : SameSemanticPublic s out) :
    Stage2SameBytes request a candidate bytes ∧
      SemanticPublicWire.parsePublic (bytes.val.map RawBridge431.rawByte) = some supplied := by
  refine ⟨⟨out, hr, ?_⟩, serializer_supplied_public s bytes supplied hs hguard hbind⟩
  change s = toSerializer out at heq
  rw [← heq]
  exact hs

/-- R8 fixes the entire transfer argument, including both output commitments. -/
theorem reconstruct_transfer_projection
    (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1)
    (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (hp : request.«public» = .PrivateTransfer p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out)) :
    toSerializer out = .Transfer (toTransfer p)
      (toTransition (AdapterReconstructSuccess.common a candidate).lane_transition) := by
  obtain ⟨he, _, _⟩ := TransferBindings.reconstruct_transfer_payload request a candidate out p hp hr
  rw [he]
  rfl

#print axioms parsePublic_of_wire_decode
#print axioms transfer_payment_guard
#print axioms hbind_of_wire
#print axioms serializer_supplied_public
#print axioms same_public_unique_bytes
#print axioms r9_of_same_public
#print axioms reconstruct_transfer_projection
end AspisR1AdapterReconstruct.StageBinding
