import NDM_ProjectionLaw
set_option autoImplicit false
namespace NDM_CommonWindows
open Aeneas Aeneas.Std Result
open AdapterRw.aspis_statement.pool_v1

def Window {T : Type} {n : Usize} (x y : Array T n) : Prop :=
 ∀ i (hx : i<x.val.length) (hy : i<y.val.length), x.val[i]=y.val[i]

theorem array_ext {T : Type} {n : Usize} (x y : Array T n) (h : Window x y) : x=y := by
 apply Subtype.ext
 exact List.ext_getElem (x.property.trans y.property.symm) h

def Nested {T : Type} {n m : Usize} (x y : Array (Array T m) n) : Prop :=
 ∀ i (hx : i<x.val.length) (hy : i<y.val.length), Window x.val[i] y.val[i]

theorem nested_ext {T : Type} {n m : Usize} (x y : Array (Array T m) n)
 (h : Nested x y) : x=y := by
 apply array_ext
 intro i hx hy
 exact array_ext _ _ (h i hx hy)

abbrev Live := pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Candidate := NDM_CommonCarrier.Candidate
abbrev Common := NDM_CommonCarrier.Common

theorem live_ext (x y : Live) (pool : x.pool=y.pool) (domain : x.deployment_domain=y.deployment_domain)
 (sequence : x.sequence=y.sequence) (next : x.next_pair_index=y.next_pair_index)
 (root : x.current_root=y.current_root) (frontier : x.frontier=y.frontier) : x=y := by
 cases x
 cases y
 simp_all

theorem candidate_ext (x y : Candidate) (next : x.next_pair_index=y.next_pair_index)
 (root : x.next_root=y.next_root) (frontier : x.next_frontier=y.next_frontier) : x=y := by
 cases x
 cases y
 simp_all

structure Fields (x y : Common) : Prop where
 master : Window x.master_account y.master_account
 checkpoint : Window x.checkpoint_account y.checkpoint_account
 lane : Window x.selected_lane_account y.selected_lane_account
 output : x.output_lane=y.output_lane
 sequence : x.checkpoint_sequence=y.checkpoint_sequence
 anchor : Window x.historical_global_anchor y.historical_global_anchor
 livePool : Window x.lane_transition.live_snapshot.pool y.lane_transition.live_snapshot.pool
 liveDomain : Window x.lane_transition.live_snapshot.deployment_domain y.lane_transition.live_snapshot.deployment_domain
 liveSequence : x.lane_transition.live_snapshot.sequence=y.lane_transition.live_snapshot.sequence
 liveNext : x.lane_transition.live_snapshot.next_pair_index=y.lane_transition.live_snapshot.next_pair_index
 liveRoot : Window x.lane_transition.live_snapshot.current_root y.lane_transition.live_snapshot.current_root
 liveFrontier : Nested x.lane_transition.live_snapshot.frontier y.lane_transition.live_snapshot.frontier
 candidateNext : x.lane_transition.candidate_afterstate.next_pair_index=y.lane_transition.candidate_afterstate.next_pair_index
 candidateRoot : Window x.lane_transition.candidate_afterstate.next_root y.lane_transition.candidate_afterstate.next_root
 candidateFrontier : Nested x.lane_transition.candidate_afterstate.next_frontier y.lane_transition.candidate_afterstate.next_frontier

/-- Pure finite extensionality. Native windows must cover the same arbitrary pre-state. -/
theorem assemble (x y : Common) (h : Fields x y) : x=y := by
 apply NDM_CommonCarrier.project_injective
 simp only [NDM_CommonCarrier.project,Prod.mk.injEq]
 exact ⟨array_ext _ _ h.master,array_ext _ _ h.checkpoint,array_ext _ _ h.lane,
 h.output,h.sequence,array_ext _ _ h.anchor,
 live_ext _ _ (array_ext _ _ h.livePool) (array_ext _ _ h.liveDomain) h.liveSequence h.liveNext
 (array_ext _ _ h.liveRoot) (nested_ext _ _ h.liveFrontier),
 candidate_ext _ _ h.candidateNext (array_ext _ _ h.candidateRoot) (nested_ext _ _ h.candidateFrontier)⟩

#print axioms array_ext
#print axioms nested_ext
#print axioms live_ext
#print axioms candidate_ext
#print axioms assemble
end NDM_CommonWindows
