import ExtractedPreparationSerializerWhole

/-! The actual public_transcript success supplies PublicBinding's hs. Fixed
carrier copies preserve all serializer fields. Decoder reachability is a
separate caller obligation; custody is not a premise of this proof. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.PreparationBinding
open AspisR1 AspisR1PublicSerializer
open AspisR1TerminalDecoder
open SerializerWhole

def fromTransition (t : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
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

def fromTransfer (p : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    recipient_commitment := p.recipient_commitment
    change_commitment := p.change_commitment }

def fromWithdrawal (p : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

def fromCommon (c : PublicBinding.Common) :
    AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  { master_account := c.master_account
    checkpoint_account := c.checkpoint_account
    selected_lane_account := c.selected_lane_account
    output_lane := c.output_lane
    checkpoint_sequence := c.checkpoint_sequence
    historical_global_anchor := c.historical_global_anchor
    lane_transition := fromTransition c.lane_transition }

def fromStatement : PublicBinding.Statement →
    AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
  | .PrivateTransfer c p => .PrivateTransfer (fromCommon c) (fromTransfer p)
  | .Withdrawal c p => .Withdrawal (fromCommon c) (fromWithdrawal p)

/-- Same fixed selector as the actual semantic_public method. -/
def preparationPublic : PublicBinding.Statement →
    AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
  | .PrivateTransfer c p => .Transfer (fromTransfer p) (fromTransition c.lane_transition)
  | .Withdrawal c p => .Withdrawal (fromWithdrawal p) (fromTransition c.lane_transition)

theorem actual_selector_eq (s : PublicBinding.Statement) :
    AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      (fromStatement s) = ok (preparationPublic s) := by
  cases s <;> rfl

theorem projection_eq (s : PublicBinding.Statement) :
    toOld (preparationPublic s) = PublicBinding.toSerializer s := by
  cases s <;> rfl

/-- No serializer-success assumption: helper success produces the same bytes. -/
theorem helper_supplies_serializer_success
    {H : Type} (D : aspis_core.Digest32 H) (s : PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (h : r1_semantic.public_transcript D (preparationPublic s) hash c1 = ok (.Ok out)) :
    ∃ bytes : alloc.vec.Vec U8,
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (PublicBinding.toSerializer s) = ok (.Ok bytes) ∧
      r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) c1 =
        ok (.Ok out) := by
  obtain ⟨bytes, hs, ht⟩ := PreparationSuccess.public_transcript_success D
    (preparationPublic s) hash c1 out h
  refine ⟨bytes, ?_, ht⟩
  rw [← projection_eq s, serializer_eq, hs]
  rfl

/-- Both ASF8 variants; hd is the remaining actual caller reachability fact. -/
theorem decoder_helper_parsePublic
    {H : Type} (D : aspis_core.Digest32 H) (asf8 : Slice U8)
    (s : PublicBinding.Statement) (hash : H) (c1 : Array U8 32#usize)
    (out : r1_wire.SemanticTranscript H)
    (hd : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      asf8 = ok (.Ok s))
    (h : r1_semantic.public_transcript D (preparationPublic s) hash c1 = ok (.Ok out)) :
    ∃ bytes wire,
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (PublicBinding.toSerializer s) = ok (.Ok bytes) ∧
      PublicSourceRaw.toWire (PublicBinding.projectRaw s) = some wire ∧
      SemanticPublicWire.parsePublic (bytes.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) ∧
      r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) c1 =
        ok (.Ok out) := by
  obtain ⟨bytes, hs, ht⟩ := helper_supplies_serializer_success D s hash c1 out h
  obtain ⟨wire, hw, hp⟩ := PublicBinding.decoder_serializer_parsePublic asf8 s bytes hd hs
  exact ⟨bytes, wire, hs, hw, hp, ht⟩

#print axioms actual_selector_eq
#print axioms projection_eq
#print axioms helper_supplies_serializer_success
#print axioms decoder_helper_parsePublic
end AspisR1PublicPreparation.PreparationBinding
