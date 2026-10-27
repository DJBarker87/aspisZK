import R1Z.PV_CB_CanonicalArrays
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalUpdate
open Aeneas Aeneas.Std Result

theorem list_set {A : Type} (predicate : A → Prop) (xs : List A) (index : Nat)
    (value : A) (valid : ∀ x ∈ xs, predicate x) (vvalue : predicate value) :
    ∀ x ∈ xs.set index value, predicate x := by
  induction xs generalizing index with
  | nil =>
    intro x member
    simp only [List.set_nil,List.not_mem_nil] at member
  | cons head tail ih =>
    intro x member
    cases index with
    | zero =>
      simp only [List.set_cons_zero,List.mem_cons] at member
      rcases member with rfl | member
      · exact vvalue
      · exact valid _ (List.mem_cons_of_mem _ member)
    | succ index =>
      simp only [List.set_cons_succ,List.mem_cons] at member
      rcases member with rfl | member
      · exact valid _ (List.mem_cons_self ..)
      · exact ih index (fun x h => valid x (List.mem_cons_of_mem _ h)) x member

theorem update {A : Type} {n : Usize} (predicate : A → Prop) (values : Array A n)
    (index : Usize) (value : A) (bound : index.val < n.val)
    (valid : PV_CB_CanonicalArrays.Valid predicate values) (vvalue : predicate value) :
    ∃ out, Array.update values index value = ok out ∧ PV_CB_CanonicalArrays.Valid predicate out := by
  have inside : index.val < values.val.length := by rw [values.property]; exact bound
  obtain ⟨out,hout,hset⟩ := WP.spec_imp_exists (Array.update_spec values index value inside)
  refine ⟨out,hout,?_⟩
  rw [hset]
  exact list_set predicate values.val index.val value valid vvalue
#print axioms list_set
#print axioms update
end R1Z.PV_CB_CanonicalUpdate
