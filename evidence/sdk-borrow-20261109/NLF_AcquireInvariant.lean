import NLF_Invariant
set_option autoImplicit false
namespace NLF_ParentModel
open NLF_RefCell NLF_SdkModel

theorem shared_preserves (p : Parent) (a : Nat) (h : Invariant p) :
    Invariant (acquire p a .shared).1 := by
  let i := (p.state.accounts a).data
  have hf := (fresh p.state p.next i h.2.1).1
  by_cases allowed : (p.state.cells i).writer = none ∧
      (p.state.cells i).readers.length < 9223372036854775807
  · have r := shared_result p.state i p.next allowed.1 hf allowed.2
    change Invariant (⟨(wrap p.state i p.next .shared).1,p.next+1,
      p.events ++ [.acquire a p.next .shared (wrap p.state i p.next .shared).2]⟩ : Parent)
    rw [r]
    apply insert_invariant p.state _ p.next i h
    · exact put_valid _ _ _ h.1 (shared_valid (p.state.cells i) p.next (h.1 i) hf allowed.1 allowed.2).2
    · exact shared_inserts p.state i p.next
  · have bad : shared (p.state.cells i) p.next = .error .conflict := by
      simp only [shared]; split_ifs with hs
      · exact False.elim (allowed ⟨hs.1,hs.2.1⟩)
      · rfl
    have r := wrapper_error p.state i p.next .shared bad
    change Invariant (⟨(wrap p.state i p.next .shared).1,p.next+1,
      p.events ++ [.acquire a p.next .shared (wrap p.state i p.next .shared).2]⟩ : Parent)
    rw [r]
    exact ⟨h.1,below_succ _ _ h.2.1,h.2.2⟩

theorem exclusive_preserves (p : Parent) (a : Nat) (h : Invariant p) :
    Invariant (acquire p a .exclusive).1 := by
  let i := (p.state.accounts a).data
  by_cases allowed : (p.state.cells i).writer = none ∧ (p.state.cells i).readers = []
  · have r := exclusive_result p.state i p.next allowed.1 allowed.2
    change Invariant (⟨(wrap p.state i p.next .exclusive).1,p.next+1,
      p.events ++ [.acquire a p.next .exclusive (wrap p.state i p.next .exclusive).2]⟩ : Parent)
    rw [r]
    apply insert_invariant p.state _ p.next i h
    · exact put_valid _ _ _ h.1 (exclusive_valid (p.state.cells i) p.next allowed.1 allowed.2).2
    · exact exclusive_inserts p.state i p.next
  · have bad : exclusive (p.state.cells i) p.next = .error .conflict := by simp [exclusive,allowed]
    have r := wrapper_error p.state i p.next .exclusive bad
    change Invariant (⟨(wrap p.state i p.next .exclusive).1,p.next+1,
      p.events ++ [.acquire a p.next .exclusive (wrap p.state i p.next .exclusive).2]⟩ : Parent)
    rw [r]
    exact ⟨h.1,below_succ _ _ h.2.1,h.2.2⟩

theorem acquire_preserves (p : Parent) (a : Nat) (k : Kind) (h : Invariant p) :
    Invariant (acquire p a k).1 := by
  cases k
  · exact shared_preserves p a h
  · exact exclusive_preserves p a h

#print axioms shared_preserves
#print axioms exclusive_preserves
#print axioms acquire_preserves
end NLF_ParentModel
