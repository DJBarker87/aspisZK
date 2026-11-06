import NLF_ParentModel
set_option autoImplicit false
namespace NLF_ParentModel
open NLF_RefCell NLF_SdkModel

theorem below_succ (s : State) (n : Nat) (h : Below s n) : Below s (n+1) := by
  intro i t ht; exact Nat.lt_succ_of_lt (h i t ht)

theorem subset_invariant (s s' : State) (n : Nat)
    (h : ValidState s ∧ Below s n ∧ Unique s) (v : ValidState s')
    (sub : ∀ i t, HasToken (s'.cells i) t → HasToken (s.cells i) t) :
    ValidState s' ∧ Below s' n ∧ Unique s' := by
  refine ⟨v, ?_, ?_⟩
  · intro i t ht; exact h.2.1 i t (sub i t ht)
  · intro i j t hi hj; exact h.2.2 i j t (sub i t hi) (sub j t hj)

theorem insert_invariant (s s' : State) (n cell : Nat)
    (h : ValidState s ∧ Below s n ∧ Unique s) (v : ValidState s')
    (sub : ∀ i t, HasToken (s'.cells i) t → (i=cell ∧ t=n) ∨ HasToken (s.cells i) t) :
    ValidState s' ∧ Below s' (n+1) ∧ Unique s' := by
  refine ⟨v, ?_, ?_⟩
  · intro i t ht
    rcases sub i t ht with ⟨_,htn⟩ | old
    · omega
    · exact Nat.lt_succ_of_lt (h.2.1 i t old)
  · intro i j t hi hj
    rcases sub i t hi with ⟨rfl,ht⟩ | oi <;>
      rcases sub j t hj with ⟨rfl,ht'⟩ | oj
    · rfl
    · have q := h.2.1 j t oj; omega
    · have q := h.2.1 i t oi; omega
    · exact h.2.2 i j t oi oj

theorem shared_inserts (s : State) (i n j t : Nat)
    (ht : HasToken ((put s i {s.cells i with readers := n :: (s.cells i).readers}).cells j) t) :
    (j=i ∧ t=n) ∨ HasToken (s.cells j) t := by
  by_cases eq : j=i
  · subst j
    simp only [put_same, HasToken, List.mem_cons] at ht
    rcases ht with hw | hn | hr
    · exact Or.inr (Or.inl hw)
    · exact Or.inl ⟨rfl,hn⟩
    · exact Or.inr (Or.inr hr)
  · exact Or.inr (by simpa [put,eq] using ht)

theorem exclusive_inserts (s : State) (i n j t : Nat)
    (ht : HasToken ((put s i {s.cells i with writer := some n}).cells j) t) :
    (j=i ∧ t=n) ∨ HasToken (s.cells j) t := by
  by_cases eq : j=i
  · subst j
    simp only [put_same, HasToken, Option.some.injEq] at ht
    rcases ht with hw | hr
    · exact Or.inl ⟨rfl,hw.symm⟩
    · exact Or.inr (Or.inr hr)
  · exact Or.inr (by simpa [put,eq] using ht)

#print axioms below_succ
#print axioms subset_invariant
#print axioms insert_invariant
#print axioms shared_inserts
#print axioms exclusive_inserts
end NLF_ParentModel
