import NKR_ScheduleCut
set_option autoImplicit false
namespace AspisR1.NKR_ScheduleExt
open Aeneas Aeneas.Std
open FIq_Native.pool_v1
/-- Arbitrary-coordinate native windows cover a whole array; no concrete
large-type enumeration or address-to-payload assumption. -/
theorem array {A : Type} {n : Usize} (a b : Array A n)
 (cells : ∀ i,NJB_ArrayCarrier.cell a i=NJB_ArrayCarrier.cell b i) : a=b := by
 have same : NJB_ArrayCarrier.cell a=NJB_ArrayCarrier.cell b := funext cells
 calc
  a=NJB_ArrayCarrier.array (NJB_ArrayCarrier.cell a):=(NJB_ArrayCarrier.array_cell a).symm
  _=NJB_ArrayCarrier.array (NJB_ArrayCarrier.cell b):=congrArg NJB_ArrayCarrier.array same
  _=b:=NJB_ArrayCarrier.array_cell b

theorem snapshot (a b : pair_tree_profile.PoolV1PairLiveSnapshotV1)
 (pool : a.pool=b.pool) (domain : a.deployment_domain=b.deployment_domain)
 (sequence : a.sequence=b.sequence) (index : a.next_pair_index=b.next_pair_index)
 (root : a.current_root=b.current_root) (frontier : a.frontier=b.frontier) : a=b := by
 cases a;cases b;simp_all

theorem afterstate (a b : pair_terminal.PoolV1PairVerifiedAfterstateV1)
 (index : a.next_pair_index=b.next_pair_index) (root : a.next_root=b.next_root)
 (frontier : a.next_frontier=b.next_frontier) : a=b := by
 cases a;cases b;simp_all

theorem transition (a b : pair_tree_profile.PoolV1PairLatePublicStatementV1)
 (source : a.live_snapshot=b.live_snapshot) (after : a.candidate_afterstate=b.candidate_afterstate) : a=b := by
 cases a;cases b;simp_all

theorem semanticPublic (a b : pair_forest_semantic_terminal.SemanticPublic)
 (variant : a.variant=b.variant) (pool : a.pool=b.pool)
 (domain : a.deployment_domain=b.deployment_domain) (anchor : a.anchor=b.anchor)
 (nullifier : a.nullifier=b.nullifier) (asset : a.asset_id=b.asset_id)
 (recipient : a.recipient=b.recipient) (change : a.change=b.change)
 (amount : a.withdrawal_amount=b.withdrawal_amount) (late : a.transition=b.transition) : a=b := by
 cases a;cases b;simp_all

#print axioms array
#print axioms snapshot
#print axioms afterstate
#print axioms transition
#print axioms semanticPublic
end AspisR1.NKR_ScheduleExt
