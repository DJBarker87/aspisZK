import FIo_FieldCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ArrayCanon
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
def Holds {N : Usize} (a : Array NE N) : Prop := ∀ x ∈ a.val, FIo_WideValues.Canon x

theorem read {N : Usize} (a : Array NE N) (i : Usize) (z : NE) (h : Holds a)
    (run : Array.index_usize a i=ok z) : FIo_WideValues.Canon z := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i value hget
    have same : value=z := Result.ok.inj run
    subst value
    change a.val[i.val]?=some z at hget
    exact h z (List.mem_of_getElem? hget)

theorem list_set {A : Type} (P : A → Prop) (xs : List A) (n : Nat) (z : A)
    (h : ∀ x ∈ xs,P x) (hz : P z) : ∀ x ∈ xs.set n z,P x := by
  induction xs generalizing n with
  | nil => simp
  | cons head tail ih =>
    intro x hx
    cases n with
    | zero =>
      simp only [List.set,List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hz
      · exact h x (by simp [hx])
    | succ n =>
      simp only [List.set,List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h x (by simp)
      · exact ih n (by intro x hx; exact h x (by simp [hx])) x hx

theorem update {N : Usize} (a b : Array NE N) (i : Usize) (z : NE)
    (h : Holds a) (hz : FIo_WideValues.Canon z)
    (run : Array.update a i z=ok b) : Holds b := by
  unfold Array.update at run
  split at run
  · cases run
  · have same := Result.ok.inj run
    subst b
    exact list_set FIo_WideValues.Canon a.val i.val z h hz

#print axioms read
#print axioms list_set
#print axioms update
end AspisR1.FIo_ArrayCanon
end
