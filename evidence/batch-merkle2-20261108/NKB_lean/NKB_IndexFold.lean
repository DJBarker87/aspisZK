import MultiproofConeLiveFold
import NJV_CallerBounds
import NJV_WellInput

set_option autoImplicit false
namespace NKB_IndexFold
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConeLiveLeaves MultiproofConeLivePreservation

/-- Each successful index insertion either retains d or appends exactly one. -/
theorem insert_bounds (k : Nat → Nat) (d x : Nat) :
 d≤(MultiproofConeLiveLeaves.insert k d x).2 ∧ (MultiproofConeLiveLeaves.insert k d x).2≤d+1 := by
 unfold MultiproofConeLiveLeaves.insert
 split <;> simp only <;> omega

theorem build_bounds (xs : List Nat) (k : Nat → Nat) (d : Nat) :
 d≤(build xs k d).2 ∧ (build xs k d).2≤d+xs.length := by
 induction xs generalizing k d with
 | nil => simp only [build,List.length_nil,Nat.add_zero];exact ⟨le_rfl,le_rfl⟩
 | cons x xs ih =>
   have step := insert_bounds k d x
   have tail := ih (MultiproofConeLiveLeaves.insert k d x).1 (MultiproofConeLiveLeaves.insert k d x).2
   simp only [build,List.length_cons]
   omega

theorem build_positive (xs : List Nat) (k : Nat → Nat) (d : Nat)
    (nonempty : 0<d ∨ xs≠[]) : 0<(build xs k d).2 := by
 cases xs with
 | nil => simp only [build];rcases nonempty with h|h;exact h;exact (h rfl).elim
 | cons x xs =>
   have next : 0<(MultiproofConeLiveLeaves.insert k d x).2 := by unfold MultiproofConeLiveLeaves.insert;split <;> simp_all <;> omega
   have tail := (build_bounds xs (MultiproofConeLiveLeaves.insert k d x).1 (MultiproofConeLiveLeaves.insert k d x).2).1
   change 0<(build xs (MultiproofConeLiveLeaves.insert k d x).1 (MultiproofConeLiveLeaves.insert k d x).2).2
   omega

theorem build_upper (xs : List Nat) (k : Nat → Nat) (d ceiling : Nat)
    (initial : ∀ a,a<d → k a≤ceiling) (input : ∀ x∈xs,x≤ceiling) :
 ∀ a,a<(build xs k d).2 → (build xs k d).1 a≤ceiling := by
 induction xs generalizing k d with
 | nil => exact initial
 | cons x xs ih =>
   exact ih (MultiproofConeLiveLeaves.insert k d x).1 (MultiproofConeLiveLeaves.insert k d x).2
     (insert_upper k d x ceiling initial (input x (by simp)))
     (fun y hy => input y (by simp only [List.mem_cons];exact Or.inr hy))

/-- Caller producer facts, before node_count: both batch sizes retain their
own bounds, and no statement that twelve implies ten occurs. Local fold success
is an intermediate observation to be supplied by the parent's same-call chain;
this lemma is not an admitted row root. -/
theorem producer (leaves : List MultiproofConeLiveFold.Leaf)
    (before after : reference.Scratch) (empty : before.n.val=0)
    (nonempty : leaves≠[]) (size : leaves.length≤12)
    (ordered : (leaves.map (fun x => x.1.val)).Pairwise (·≤·))
    (canonical : ∀ leaf∈leaves,leaf.1.val<262144)
    (returned : MultiproofConeLiveFold.fold leaves before=ok (some after)) :
 0<after.n.val ∧ after.n.val≤leaves.length ∧
 MultiproofConeLiveOrder.Strict (keys after) 0 after.n.val ∧
 (∀ a,a<after.n.val → keys after a<262144) := by
 have projection := MultiproofConeLiveFold.fold_projection leaves before after (by omega) returned
 have first := congrArg Prod.fst projection
 have second := congrArg Prod.snd projection
 change keys after=(build (leaves.map (fun x => x.1.val)) (keys before) before.n.val).1 at first
 change after.n.val=(build (leaves.map (fun x => x.1.val)) (keys before) before.n.val).2 at second
 rw [empty] at first second
 have count := build_bounds (leaves.map (fun x => x.1.val)) (keys before) 0
 have positive := build_positive (leaves.map (fun x => x.1.val)) (keys before) 0
   (Or.inr (by intro h;have len:=congrArg List.length h;simp only [List.length_map,List.length_nil] at len;exact nonempty (List.length_eq_zero_iff.mp len)))
 have upper := build_upper (leaves.map (fun x => x.1.val)) (keys before) 0 262143
   (by intro a h;omega) (by
     intro x hx
     obtain ⟨leaf,member,rfl⟩ := List.mem_map.mp hx
     have bound := canonical leaf member
     omega)
 refine ⟨by omega,by simpa only [List.length_map,Nat.zero_add,←second] using count.2,
   MultiproofConeLiveFold.fold_sorted leaves before after empty (by omega) ordered returned,?_⟩
 intro a ha
 rw [first]
 have bound := upper a (by rw [←second];exact ha)
 omega

#print axioms insert_bounds
#print axioms build_bounds
#print axioms build_positive
#print axioms build_upper
#print axioms producer
end NKB_IndexFold
