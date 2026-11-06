import NJG_Carriers
set_option autoImplicit false
namespace AspisR1.NJG_InputCarriers
open Aeneas Aeneas.Std Result

def upWithdrawal (v : NIX_EmittedTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨v.pool,v.deployment_domain,v.anchor_sequence,v.anchor_root,v.nullifier,v.asset_id,v.amount,v.destination_token_account,v.change_commitment⟩

def downWithdrawal (v : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : NIX_EmittedTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨v.pool,v.deployment_domain,v.anchor_sequence,v.anchor_root,v.nullifier,v.asset_id,v.amount,v.destination_token_account,v.change_commitment⟩

theorem withdrawal_roundtrip (v : NIX_EmittedTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : downWithdrawal (upWithdrawal v)=v := by cases v;rfl

def upTransfer (v : NIX_EmittedTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨v.pool,v.deployment_domain,v.anchor_sequence,v.anchor_root,v.nullifier,v.asset_id,v.recipient_commitment,v.change_commitment⟩

def downTransfer (v : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : NIX_EmittedTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨v.pool,v.deployment_domain,v.anchor_sequence,v.anchor_root,v.nullifier,v.asset_id,v.recipient_commitment,v.change_commitment⟩

theorem transfer_roundtrip (v : NIX_EmittedTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : downTransfer (upTransfer v)=v := by cases v;rfl

def upLive (v : NIX_EmittedTypes.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨v.pool,v.deployment_domain,v.sequence,v.next_pair_index,v.current_root,v.frontier⟩

def downLive (v : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : NIX_EmittedTypes.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨v.pool,v.deployment_domain,v.sequence,v.next_pair_index,v.current_root,v.frontier⟩

theorem live_roundtrip (v : NIX_EmittedTypes.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : downLive (upLive v)=v := by cases v;rfl

def upAfter (v : NIX_EmittedTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨v.next_pair_index,v.next_root,v.next_frontier⟩

def downAfter (v : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : NIX_EmittedTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨v.next_pair_index,v.next_root,v.next_frontier⟩

theorem after_roundtrip (v : NIX_EmittedTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : downAfter (upAfter v)=v := by cases v;rfl

def upLate (v : NIX_EmittedTypes.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
 AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 := ⟨upLive v.live_snapshot,upAfter v.candidate_afterstate⟩
def downLate (v : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
 NIX_EmittedTypes.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 := ⟨downLive v.live_snapshot,downAfter v.candidate_afterstate⟩

theorem late_roundtrip (v : NIX_EmittedTypes.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
 downLate (upLate v)=v := by cases v;simp only [upLate,downLate,live_roundtrip,after_roundtrip]

abbrev EP := NIX_EmittedTypes.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev MP := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public

def upPublic : EP→MP
 | .Transfer payment late=>.Transfer (upTransfer payment) (upLate late)
 | .Withdrawal payment late=>.Withdrawal (upWithdrawal payment) (upLate late)
def downPublic : MP→EP
 | .Transfer payment late=>.Transfer (downTransfer payment) (downLate late)
 | .Withdrawal payment late=>.Withdrawal (downWithdrawal payment) (downLate late)

theorem public_roundtrip (v : EP) : downPublic (upPublic v)=v := by
 cases v <;> simp only [upPublic,downPublic,transfer_roundtrip,withdrawal_roundtrip,late_roundtrip]

def upPrefix (v : NIX_EmittedTypes.r1_wire.Prefix) : AspisR1PublicPreparation.r1_wire.Prefix := ⟨v.c1_root,v.records⟩
def downPrefix (v : AspisR1PublicPreparation.r1_wire.Prefix) : NIX_EmittedTypes.r1_wire.Prefix := ⟨v.c1_root,v.records⟩

theorem prefix_roundtrip (v : NIX_EmittedTypes.r1_wire.Prefix) : downPrefix (upPrefix v)=v := by cases v;rfl

def upDigest {H : Type} (D : NIX_EmittedTypes.aspis_core.digest.Digest32 H) : AspisR1PublicPreparation.aspis_core.Digest32 H := ⟨D.coremarkerCopyInst,D.digest⟩
def downDigest {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) : NIX_EmittedTypes.aspis_core.digest.Digest32 H := ⟨D.coremarkerCopyInst,D.digest⟩

theorem digest_roundtrip {H : Type} (D : NIX_EmittedTypes.aspis_core.digest.Digest32 H) : downDigest (upDigest D)=D := by cases D;rfl

/-- The same digest receives identical byte slices and returns the complete
same reply. No digest value or totality law is added. -/
theorem digest_call {H : Type} (D : NIX_EmittedTypes.aspis_core.digest.Digest32 H) (hash : H) (parts : Slice (Slice U8)) :
 (upDigest D).digest hash parts=D.digest hash parts := rfl

#print axioms withdrawal_roundtrip
#print axioms transfer_roundtrip
#print axioms live_roundtrip
#print axioms after_roundtrip
#print axioms late_roundtrip
#print axioms public_roundtrip
#print axioms prefix_roundtrip
#print axioms digest_roundtrip
#print axioms digest_call
end AspisR1.NJG_InputCarriers
