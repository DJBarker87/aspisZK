import OccupancyGeneratedSlice
import PreparationPublicFieldsCanonical

/-!
Focused constructor cut for the sealed terminal candidate Funs source
(Funs.lean SHA 04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e,
`private_public` lines 1021-1035 and `withdrawal_public` lines 999-1013).
The retained carrier declarations are OccupancyGeneratedSlice (Types SHA
60cf4b447bc2e9d57d58fc2b1386e91120fa6fb26961e725690ac09da4ac6713). The
definitions below are the exact direct field copies after projecting the
candidate input structs. This module does not claim the whole candidate Funs
module or terminal caller was compiled here.
-/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
open AspisR1SelectedMaskProbe

abbrev SemanticPublic :=
  pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev CandidateTransition :=
  pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def fromWholeTransition (t : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : CandidateTransition :=
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

def toWholeTransition (t : CandidateTransition) : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
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

theorem transition_roundtrip (t : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    toWholeTransition (fromWholeTransition t) = t := by
  cases t with
  | mk live after => cases live; cases after; rfl

/-- Direct source constructor copy, with its transfer input already projected
to the serializer carrier. -/
def privatePublicCopy (p : AspisR1PublicSerializer.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) (t : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : SemanticPublic :=
  { variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer
    pool := p.pool
    deployment_domain := p.deployment_domain
    anchor := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    recipient := some p.recipient_commitment
    change := p.change_commitment
    withdrawal_amount := none
    transition := fromWholeTransition t }

/-- Direct source constructor copy, with its withdrawal input already
projected to the serializer carrier. -/
def withdrawalPublicCopy (p : AspisR1PublicSerializer.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) (t : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : SemanticPublic :=
  { variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal
    pool := p.pool
    deployment_domain := p.deployment_domain
    anchor := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    recipient := none
    change := p.change_commitment
    withdrawal_amount := some p.amount
    transition := fromWholeTransition t }

def toWholePublic (p : SemanticPublic) : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  match p.variant with
  | .PrivateTransfer =>
      .Transfer
        { pool := p.pool
          deployment_domain := p.deployment_domain
          anchor_sequence := 0#u64
          anchor_root := p.anchor
          nullifier := p.nullifier
          asset_id := p.asset_id
          recipient_commitment := p.recipient.getD (Array.make 8#usize [0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32])
          change_commitment := p.change }
        (toWholeTransition p.transition)
  | .Withdrawal =>
      .Withdrawal
        { pool := p.pool
          deployment_domain := p.deployment_domain
          anchor_sequence := 0#u64
          anchor_root := p.anchor
          nullifier := p.nullifier
          asset_id := p.asset_id
          amount := p.withdrawal_amount.getD 0#u32
          destination_token_account := Array.make 32#usize [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
          change_commitment := p.change }
        (toWholeTransition p.transition)

theorem privatePublicCopy_toWhole_projection (p : AspisR1PublicSerializer.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) (t : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
      (toWholePublic (privatePublicCopy p t)) =
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw (.Transfer p t) := by
  cases p with
  | mk pool domain seq anchor nullifier asset recipient change =>
    simp [toWholePublic, privatePublicCopy,
      AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw,
      AspisR1PublicSerializer.RawBridge431.project,
      AspisR1PublicSerializer.RawBridge431.projectCommon,
      AspisR1PublicSerializer.RawBridge431.projectDigest,
      AspisR1PublicSerializer.RawBridge431.projectFrontier,
      fromWholeTransition, toWholeTransition]

theorem withdrawalPublicCopy_toWhole_projection (p : AspisR1PublicSerializer.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) (t : AspisR1PublicSerializer.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
      (toWholePublic (withdrawalPublicCopy p t)) =
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw (.Withdrawal p t) := by
  cases p with
  | mk pool domain seq anchor nullifier asset amount destination change =>
    simp [toWholePublic, withdrawalPublicCopy,
      AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw,
      AspisR1PublicSerializer.RawBridge431.project,
      AspisR1PublicSerializer.RawBridge431.projectCommon,
      AspisR1PublicSerializer.RawBridge431.projectDigest,
      AspisR1PublicSerializer.RawBridge431.projectFrontier,
      fromWholeTransition, toWholeTransition]

def copyFromWhole (w : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public) : SemanticPublic :=
  match w with
  | .Transfer p t => privatePublicCopy p t
  | .Withdrawal p t => withdrawalPublicCopy p t

theorem copyFromWhole_projection (w : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
      (toWholePublic (copyFromWhole w)) =
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
      w := by
  cases w with
  | Transfer p t => exact privatePublicCopy_toWhole_projection p t
  | Withdrawal p t => exact withdrawalPublicCopy_toWhole_projection p t

def copyFromStatement (s : AspisR1TerminalDecoder.PublicBinding.Statement) : SemanticPublic :=
  copyFromWhole (AspisR1TerminalDecoder.PublicBinding.toSerializer s)

theorem copyFromStatement_projection (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
      (toWholePublic (copyFromStatement s)) =
    AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
      (AspisR1TerminalDecoder.PublicBinding.toSerializer s) := by
  exact copyFromWhole_projection
    (AspisR1TerminalDecoder.PublicBinding.toSerializer s)

theorem copied_candidate_projection_is_canonical
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize)
    (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = ok (.Ok out)) :
    AspisR1.PublicSourceRaw.Canonical
      (AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
        (toWholePublic (copyFromStatement s))) := by
  have hcanonical :=
    AspisR1PublicPreparation.ActualPublicFieldBounds.public_transcript_fields_canonical
      D s hash c1 out h
  simpa [AspisR1TerminalDecoder.PublicBinding.projectRaw] using
    (copyFromStatement_projection s).symm ▸ hcanonical

#print axioms transition_roundtrip
#print axioms privatePublicCopy_toWhole_projection
#print axioms withdrawalPublicCopy_toWhole_projection
#print axioms copyFromStatement_projection
#print axioms copied_candidate_projection_is_canonical
end AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
