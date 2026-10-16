import ExtractedPreparationSerializerLoop
import ExtractedDecoderPublicBinding

/-! All-outcome transport of the actual preparation serializer into the checked
serializer carrier. This supplies the serializer success witness from helper
success; no custody premise is involved. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.SerializerWhole
open SerializerFields SerializerLoop

def mapOutcome {α : Type} : Result (core.result.Result α NewError) →
    Result (core.result.Result α OldError)
  | .ok r => .ok (mapStatus r)
  | .fail e => .fail e
  | .div => .div

private theorem map_bind {α β : Type} (m : Result α)
    (k : α → Result (core.result.Result β NewError)) :
    mapOutcome (do let x ← m; k x) = (do let x ← m; mapOutcome (k x)) := by
  cases m <;> rfl

private theorem map_pair_bind {α : Type} (m : Result α)
    (k : α → Result (core.result.Result Unit NewError × ByteVec)) :
    mapPairOutcome (do let x ← m; k x) = (do let x ← m; mapPairOutcome (k x)) := by
  cases m <;> rfl

private theorem map_pair_ok {α : Type} (r : core.result.Result α NewError) (out : ByteVec) :
    mapPairOutcome (ok (r, out)) = ok (mapStatus r, out) := rfl

private theorem map_outcome_ok {α : Type} (r : core.result.Result α NewError) :
    mapOutcome (ok r) = ok (mapStatus r) := rfl

private theorem bind_map_pair {α β : Type}
    (m : Result (core.result.Result α NewError × ByteVec))
    (k : core.result.Result α OldError × ByteVec → Result β) :
    (do let x ← mapPairOutcome m; k x) =
      (do let x ← m; k (mapStatus x.1, x.2)) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok pair => cases pair; rfl

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

macro "transport_serializer" : tactic => `(tactic|
  repeat' first
    | rfl
    | (fail_if_no_progress simp only [fields_eq, bind_map_pair, map_pair_bind, map_bind,
        uncurry_apply_pair, mapStatus, map_pair_ok, map_outcome_ok,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok])
    | (apply bind_pair_congr; intro status out; cases status)
    | (apply bind_congr; intro x))

theorem frontier_eq (out : ByteVec)
    (values : Array (Array U32 8#usize) 20#usize) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values =
      mapPairOutcome (pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out values) := by
  unfold AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
    pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
  transport_serializer

def toTransition (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    AspisR1PublicSerializer.Whole431.Transition :=
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

def toTransfer (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    AspisR1PublicSerializer.Whole431.Transfer :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    recipient_commitment := p.recipient_commitment
    change_commitment := p.change_commitment }

def toWithdrawal (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    AspisR1PublicSerializer.Whole431.Withdrawal :=
  { pool := p.pool
    deployment_domain := p.deployment_domain
    anchor_sequence := p.anchor_sequence
    anchor_root := p.anchor_root
    nullifier := p.nullifier
    asset_id := p.asset_id
    amount := p.amount
    destination_token_account := p.destination_token_account
    change_commitment := p.change_commitment }

def toOld : pool_v1.pair_forest_semantic_terminal.r0.Public →
    AspisR1PublicSerializer.Whole431.Public
  | .Transfer p t => .Transfer (toTransfer p) (toTransition t)
  | .Withdrawal p t => .Withdrawal (toWithdrawal p) (toTransition t)

/-- Exact outcomes for every carrier, including allocation failure and errors. -/
theorem serializer_eq (p : pool_v1.pair_forest_semantic_terminal.r0.Public) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (toOld p) =
      mapOutcome (pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p) := by
  cases p <;>
    simp only [toOld,
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes,
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic,
      pool_v1.pair_forest_semantic_terminal.r0.Public.semantic,
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.private_public,
      pool_v1.pair_forest_semantic_terminal.private_public,
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.withdrawal_public,
      pool_v1.pair_forest_semantic_terminal.withdrawal_public,
      toTransfer, toWithdrawal, toTransition, bind_tc_ok] <;>
    simp only [frontier_eq] <;>
    transport_serializer

#print axioms frontier_eq
#print axioms serializer_eq
end AspisR1PublicPreparation.SerializerWhole
