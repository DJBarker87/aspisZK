import R1Z.ProverRwQueryScan
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RJQ_QueryInvariant
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]
def Bounded (q : Queries) : Prop := ∀ x ∈ q.val, x.val < 262144

theorem mask (x : U32) : (x &&& 262143#u32).val < 262144 := by
  rw [UScalar.val_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem set_bounded (xs : List U32) (i : Nat) (x : U32)
    (hx : x.val < 262144) (hs : ∀ y ∈ xs, y.val < 262144) :
    ∀ y ∈ xs.set i x, y.val < 262144 := by
  induction xs generalizing i with
  | nil => simp only [List.set_nil, List.not_mem_nil, false_implies, implies_true]
  | cons a xs ih =>
    cases i with
    | zero =>
      intro y hy
      simp only [List.set_cons_zero, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact hs y (List.mem_cons_of_mem a hy)
    | succ i =>
      intro y hy
      simp only [List.set_cons_succ, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hs _ (List.mem_cons_self)
      · exact ih i (fun z hz => hs z (List.mem_cons_of_mem a hz)) y hy

theorem update (q : Queries) (i : Usize) (x : U32) (hq : Bounded q)
    (hx : x.val < 262144) : Post Bounded (Array.update q i x) := by
  intro out h
  unfold Array.update at h
  split at h
  · cases h
  · cases h
    exact set_bounded q.val i.val x hx hq

theorem initial : Bounded (Array.repeat 22#usize 0#u32) := by
  intro x hx
  have h : x = 0#u32 := (by simpa only [Array.repeat, List.mem_replicate] using hx : (22#usize).val ≠ 0 ∧ x = 0#u32).2
  rw [h]
  decide

#print axioms initial
#print axioms mask
#print axioms set_bounded
#print axioms update
end R1Z.PV_RJQ_QueryInvariant
