import NHB_Membership
set_option autoImplicit false
namespace AspisR1.NHB_Partition
open Aeneas Aeneas.Std

theorem witness (xs : List U32) (n : Nat) (x : U32) :
    x ∈ xs.take n ↔ ∃ i, i<n ∧ xs[i]?=some x := by
  induction xs generalizing n with
  | nil => simp
  | cons y ys ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons,List.mem_cons]
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨0,by omega,by simpa using congrArg some h.symm⟩
        · obtain ⟨i,hi,he⟩ := (ih n).mp h
          exact ⟨i+1,by omega,by simpa using he⟩
      · rintro ⟨i,hi,he⟩
        cases i with
        | zero =>
          have eq : y=x := by simpa using he
          exact Or.inl eq.symm
        | succ i =>
          exact Or.inr ((ih n).mpr ⟨i,by omega,by simpa using he⟩)

theorem absent (xs : List U32) (n : Nat) (x : U32) :
    NHB_Membership.reference x (xs.take n)=false ↔
      ∀ i, i<n → xs[i]?≠some x := by
  constructor
  · intro no i hi he
    have mem := (witness xs n x).mpr ⟨i,hi,he⟩
    rw [NHB_Membership.reference_eq] at no
    simp only [mem,decide_true] at no
    cases no
  · intro no
    have notmem : x ∉ xs.take n := by
      intro mem
      obtain ⟨i,hi,he⟩ := (witness xs n x).mp mem
      exact no i hi he
    rw [NHB_Membership.reference_eq]
    simp only [notmem,decide_false]

/-- Every query is covered without a successful-native-result precondition. -/
theorem complete (xs : List U32) (n : Nat) (x : U32) :
    (∃ i, i<n ∧ xs[i]?=some x) ∨ (∀ i, i<n → xs[i]?≠some x) := by
  by_cases mem : x ∈ xs.take n
  · exact Or.inl ((witness xs n x).mp mem)
  · exact Or.inr ((absent xs n x).mp (by
      rw [NHB_Membership.reference_eq]
      simp only [mem,decide_false]))

#print axioms witness
#print axioms absent
#print axioms complete
end AspisR1.NHB_Partition
