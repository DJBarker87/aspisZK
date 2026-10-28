import R1Z.BuilderPublicExtracted
import R1Z.BuilderCanonical

/-! The two actual shipped public projection functions, extracted directly.
The projection retains both snapshot and afterstate; context byte fields stay
in the enclosing source record. Admission and output trace identity are not
inferred from the fact that this projection is total. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderPublicProjection
open Aeneas Aeneas.Std Result AspisBuilderPublicSource
open pool_v1.pair_forest_semantic_terminal
open R0Z.WriterRefine R1J.SpendWitnessMap
abbrev Transfer := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev Transition := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def semanticPublic (p : SemanticPublic) : R0P.Public F where
  variant := match p.variant with
    | .PrivateTransfer => .privateTransfer
    | .Withdrawal => .withdrawal
  anchor := digK p.anchor
  nullifier := digK p.nullifier
  assetId := liftU p.asset_id
  recipient := p.recipient.map digK
  change := digK p.change
  withdrawalAmount := p.withdrawal_amount.map liftU
  nextPairIndex := p.transition.live_snapshot.next_pair_index.val
  snapshotFrontier := fun l => digK (p.transition.live_snapshot.frontier.val[l.val]!)
  nextRoot := digK p.transition.candidate_afterstate.next_root
  nextFrontier := fun l => digK (p.transition.candidate_afterstate.next_frontier.val[l.val]!)

def transferPublic (p : Transfer) (t : Transition) : R0P.Public F where
  variant := .privateTransfer
  anchor := digK p.anchor_root
  nullifier := digK p.nullifier
  assetId := liftU p.asset_id
  recipient := some (digK p.recipient_commitment)
  change := digK p.change_commitment
  withdrawalAmount := none
  nextPairIndex := t.live_snapshot.next_pair_index.val
  snapshotFrontier := fun l => digK (t.live_snapshot.frontier.val[l.val]!)
  nextRoot := digK t.candidate_afterstate.next_root
  nextFrontier := fun l => digK (t.candidate_afterstate.next_frontier.val[l.val]!)

def withdrawalPublic (p : Withdrawal) (t : Transition) : R0P.Public F where
  variant := .withdrawal
  anchor := digK p.anchor_root
  nullifier := digK p.nullifier
  assetId := liftU p.asset_id
  recipient := none
  change := digK p.change_commitment
  withdrawalAmount := some (liftU p.amount)
  nextPairIndex := t.live_snapshot.next_pair_index.val
  snapshotFrontier := fun l => digK (t.live_snapshot.frontier.val[l.val]!)
  nextRoot := digK t.candidate_afterstate.next_root
  nextFrontier := fun l => digK (t.candidate_afterstate.next_frontier.val[l.val]!)

theorem transfer_projection (p : Transfer) (t : Transition) :
    ∃ s, private_public p t = ok s ∧ semanticPublic s = transferPublic p t ∧
      s.pool = p.pool ∧ s.deployment_domain = p.deployment_domain ∧ s.transition = t :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem withdrawal_projection (p : Withdrawal) (t : Transition) :
    ∃ s, withdrawal_public p t = ok s ∧ semanticPublic s = withdrawalPublic p t ∧
      s.pool = p.pool ∧ s.deployment_domain = p.deployment_domain ∧ s.transition = t :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem transfer_success (p : Transfer) (t : Transition) (s : SemanticPublic)
    (h : private_public p t = ok s) : semanticPublic s = transferPublic p t := by
  cases Result.ok.inj h
  rfl

theorem withdrawal_success (p : Withdrawal) (t : Transition) (s : SemanticPublic)
    (h : withdrawal_public p t = ok s) : semanticPublic s = withdrawalPublic p t := by
  cases Result.ok.inj h
  rfl

theorem public_base {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
    (Fbase : Subfield K) (p : SemanticPublic) :
    R0P.PublicBase Fbase (mapPub (K := K) (semanticPublic p)) :=
  BuilderCanonical.publicBase_map Fbase _

#print axioms transfer_projection
#print axioms withdrawal_projection
#print axioms transfer_success
#print axioms withdrawal_success
#print axioms public_base
end R1Z.BuilderPublicProjection
