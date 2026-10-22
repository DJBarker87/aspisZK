import PublicCodecAgreement
import ExtractedDecoderPublicBridge

/-! Fixed carrier transport for the actual ASF8 decoder's returned statement.
The transition is copied from that statement; no equality to an independently
chosen transition or public is assumed. The two actual success equations remain
explicit until the source caller is extracted. This does not establish account
reachability, custody, or Rust/runtime preservation. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1PublicSerializer

namespace AspisR1TerminalDecoder.PublicBinding
abbrev Transition := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Statement := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Transfer := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1

/-- All six snapshot fields and all three candidate fields are retained. -/
def toTransition (t : Transition) : Whole431.Transition :=
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

def fromTransition (t : Whole431.Transition) : Transition :=
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

theorem from_to_transition (t : Transition) :
    fromTransition (toTransition t) = t := by
  cases t with
  | mk live after => cases live; cases after; rfl

theorem to_from_transition (t : Whole431.Transition) :
    toTransition (fromTransition t) = t := by
  cases t with
  | mk live after => cases live; cases after; rfl

/-- The eight transfer fields are copied without choosing a byte-derived value. -/
def toTransfer (p : Transfer) : Whole431.Transfer :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    recipient_commitment := p.recipient_commitment
    change_commitment := p.change_commitment }

/-- This fixed projection matches the variant/borrow expression in `first`.
That source observation is not a theorem about execution of `first`. -/
def toSerializer : Statement → Whole431.Public
  | .PrivateTransfer c p => .Transfer (toTransfer p) (toTransition c.lane_transition)
  | .Withdrawal c p => .Withdrawal (PublicBridge.toSerializer p)
      (toTransition c.lane_transition)

theorem transfer_projection (c : Common) (p : Transfer) :
    toSerializer (.PrivateTransfer c p) =
      .Transfer (toTransfer p) (toTransition c.lane_transition) := rfl

theorem withdrawal_projection (c : Common) (p : CallerBridge.Public) :
    toSerializer (.Withdrawal c p) =
      .Withdrawal (PublicBridge.toSerializer p) (toTransition c.lane_transition) := rfl

def projectRaw (s : Statement) : PublicSourceRaw.Public :=
  ExtractedPublicCheckedBridge432.projectRaw (toSerializer s)

/-- Computed from the fixed source-carrier projection, not from serialized bytes. -/
def computedPublic (s : Statement) : Option (R0P.Public SemanticPublicWire.M31) :=
  (PublicSourceRaw.toWire (projectRaw s)).map SemanticPublicWire.toPublic

/-- Transfer has no withdrawal amount guard; reuse the existing serializer
refinement and codec agreement without a new transfer-validator model. -/
theorem transfer_serializer_parsePublic (c : Common) (p : Transfer)
    (semantic : FieldsRefinement431.ByteVec)
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (toSerializer (.PrivateTransfer c p)) = ok (.Ok semantic)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw (.PrivateTransfer c p)) = some wire ∧
      SemanticPublicWire.parsePublic (semantic.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  have hraw := RawBridge431.extracted_refines_core
    (toSerializer (.PrivateTransfer c p)) (semantic.val.map RawBridge431.rawByte)
    ⟨semantic, hs, rfl⟩
  have hguard : PublicRawAmountGuard.PaymentAmountGuard
      (RawBridge431.project (toSerializer (.PrivateTransfer c p))) := by
    trivial
  obtain ⟨wire, hw, hd⟩ := PublicRawAmountGuardAgreement.decoded_of_guarded_core_success
    (RawBridge431.project (toSerializer (.PrivateTransfer c p)))
    (semantic.val.map RawBridge431.rawByte) hraw hguard
  exact ⟨wire, hw, PublicCodecAgreement.parsePublic_of_decode _ _ hd⟩

/-- Both ASF8 variants. The same decoded statement fixes every serializer
argument, including the full lane transition. `hd` and `hs` remain actual
computation premises; neither is replaced by an assumed validation predicate. -/
theorem decoder_serializer_parsePublic (asf8 : Slice U8) (s : Statement)
    (semantic : FieldsRefinement431.ByteVec)
    (hd : pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      asf8 = ok (.Ok s))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (toSerializer s) = ok (.Ok semantic)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw s) = some wire ∧
      SemanticPublicWire.parsePublic (semantic.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  cases s with
  | PrivateTransfer c p => exact transfer_serializer_parsePublic c p semantic hs
  | Withdrawal c p =>
    exact PublicBridge.decoder_serializer_parsePublic asf8 c p
      (toTransition c.lane_transition) semantic hd hs

/-- Equality with the computed fixed projection requires no `hbind` premise.
This computed value has not yet been identified with an actual caller input. -/
theorem decoder_serializer_eq_computed (asf8 : Slice U8) (s : Statement)
    (semantic : FieldsRefinement431.ByteVec)
    (hd : pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      asf8 = ok (.Ok s))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (toSerializer s) = ok (.Ok semantic)) :
    SemanticPublicWire.parsePublic (semantic.val.map RawBridge431.rawByte) =
      computedPublic s := by
  obtain ⟨wire, hw, hp⟩ := decoder_serializer_parsePublic asf8 s semantic hd hs
  simpa only [computedPublic, hw, Option.map_some] using hp

#print axioms from_to_transition
#print axioms to_from_transition
#print axioms transfer_projection
#print axioms withdrawal_projection
#print axioms transfer_serializer_parsePublic
#print axioms decoder_serializer_parsePublic
#print axioms decoder_serializer_eq_computed
end AspisR1TerminalDecoder.PublicBinding
