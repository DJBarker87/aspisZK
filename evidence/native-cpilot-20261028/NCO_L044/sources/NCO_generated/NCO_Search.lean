import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_Search

def search (f : Nat → Bool) (stop start : Nat) : Option Nat :=
  (List.range' start (stop-start)).find? f

theorem terminal (f : Nat → Bool) (stop start : Nat) (h : stop ≤ start) :
    search f stop start = none := by
  simp [search,Nat.sub_eq_zero_of_le h]

theorem step (f : Nat → Bool) (stop start : Nat) (h : start < stop) :
    search f stop start = if f start then some start else search f stop (start+1) := by
  have range : List.range' start (stop-start) = start :: List.range' (start+1) (stop-(start+1)) := by
    apply List.range'_eq_cons_iff.mpr
    exact ⟨rfl,by omega,by congr 1; omega⟩
  unfold search
  rw [range,List.find?_cons]

theorem from_zero (f : Nat → Bool) (stop : Nat) :
    search f stop 0 = (List.range stop).find? f := by
  simp [search,List.range'_eq_range]

#print axioms terminal
#print axioms step
#print axioms from_zero
end NCO_Search
