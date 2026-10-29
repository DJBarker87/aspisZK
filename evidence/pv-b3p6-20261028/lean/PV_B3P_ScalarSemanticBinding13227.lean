import PV_B3P_ScalarSemantic13Funs
import PV_B3P_TopDown13227
namespace PV_B3P_ScalarBinding13227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
abbrev RP := PV_B3P_ScalarSemantic13.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev RW := PV_B3P_ScalarSemantic13.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev RL := PV_B3P_ScalarSemantic13.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev RA := PV_B3P_ScalarSemantic13.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev RT := PV_B3P_ScalarSemantic13.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev RSem := PV_B3P_ScalarSemantic13.reference_terminal.SemanticPublic
abbrev PP := PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev PW := PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev After := PV_B3P_227.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Late (base : ExternalTypes) :=
  @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 (PV_B3P_Install227.Types base)

def toPrivate (p : PP) : RP :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩
def toWithdrawal (p : PW) : RW :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩
def toSnapshot (p : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : RL :=
  ⟨p.pool,p.deployment_domain,p.sequence,p.next_pair_index,p.current_root,p.frontier⟩
def toAfter (p : After) : RA := ⟨p.next_pair_index,p.next_root,p.next_frontier⟩
def toLate (base : ExternalTypes) (p : Late base) : RT :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  ⟨toSnapshot p.live_snapshot,toAfter p.candidate_afterstate⟩
def fromSemantic (p : RSem) : SP :=
  ⟨(match p.variant with | .PrivateTransfer => .PrivateTransfer | .Withdrawal => .Withdrawal),
   p.pool,p.deployment_domain,p.anchor,p.nullifier,p.asset_id,p.recipient,p.change,p.withdrawal_amount,
   ⟨⟨p.transition.live_snapshot.pool,p.transition.live_snapshot.deployment_domain,
      p.transition.live_snapshot.sequence,p.transition.live_snapshot.next_pair_index,
      p.transition.live_snapshot.current_root,p.transition.live_snapshot.frontier⟩,
    ⟨p.transition.candidate_afterstate.next_pair_index,p.transition.candidate_afterstate.next_root,
      p.transition.candidate_afterstate.next_frontier⟩⟩⟩

def private_public13 (base : ExternalTypes) (p : PP) (t : Late base) : Result SP := do
  let r ← PV_B3P_ScalarSemantic13.reference_terminal.private_public (toPrivate p) (toLate base t)
  .ok (fromSemantic r)
def withdrawal_public13 (base : ExternalTypes) (p : PW) (t : Late base) : Result SP := do
  let r ← PV_B3P_ScalarSemantic13.reference_terminal.withdrawal_public (toWithdrawal p) (toLate base t)
  .ok (fromSemantic r)

def PV_B3P_Link_private_public (base : ExternalTypes) : Prop :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  ∀ p t, private_public13 base p t = .ok (PV_B3P_Carrier227.semantic base (.Transfer p t))
def PV_B3P_Link_withdrawal_public (base : ExternalTypes) : Prop :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  ∀ p t, withdrawal_public13 base p t = .ok (PV_B3P_Carrier227.semantic base (.Withdrawal p t))

theorem private_public_binding13 (base : ExternalTypes) : PV_B3P_Link_private_public base := by
  intro p t
  rfl
theorem withdrawal_public_binding13 (base : ExternalTypes) : PV_B3P_Link_withdrawal_public base := by
  intro p t
  rfl

/-- The two source match arms, interpreted with the exact new extracted callees.
Loan/return correspondence is structural own-1 evidence, not an extractor output. -/
def semantic_source13 (base : ExternalTypes) (p : Public base) : Result SP :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  let source := match p with
    | .Transfer public1 transition => PV_B3P_ScalarSemantic13.reference_terminal.r0.Public.Transfer (toPrivate public1) (toLate base transition)
    | .Withdrawal public1 transition => PV_B3P_ScalarSemantic13.reference_terminal.r0.Public.Withdrawal (toWithdrawal public1) (toLate base transition)
  do
    let result ← PV_B3P_ScalarSemantic13.reference_terminal.r0.Public.semantic source
    .ok (fromSemantic result)

theorem semantic_source_binding13 (base : ExternalTypes) (p : Public base) :
    semantic_source13 base p = .ok (PV_B3P_Carrier227.semantic base p) := by
  cases p with
  | Transfer public1 transition => exact private_public_binding13 base public1 transition
  | Withdrawal public1 transition => exact withdrawal_public_binding13 base public1 transition

def transition_source13 (base : ExternalTypes) (p : Public base) : Result (Late base) :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  match p with
  | .Transfer _ t => .ok t
  | .Withdrawal _ t => .ok t

def PV_B3P_Link_transition (base : ExternalTypes) : Prop :=
  letI : ExternalTypes := PV_B3P_Install227.Types base
  (∀ p t, transition_source13 base (.Transfer p t) = .ok t) ∧
  (∀ p t, transition_source13 base (.Withdrawal p t) = .ok t)
theorem transition_source_binding13 (base : ExternalTypes) : PV_B3P_Link_transition base :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

def with_semantic13 (base : ExternalTypes) (native : SourcePorts base) : SourcePorts base :=
  {native with semantic := semantic_source13 base}
theorem semantic_link13 (base : ExternalTypes) (native : SourcePorts base) :
    PV_B3P_Link_semantic base (with_semantic13 base native) := semantic_source_binding13 base

#print axioms private_public_binding13
#print axioms withdrawal_public_binding13
#print axioms semantic_source_binding13
#print axioms transition_source_binding13
#print axioms semantic_link13
end
end PV_B3P_ScalarBinding13227
