import NLF_AcquireInvariant
set_option autoImplicit false
namespace NLF_ParentModel
open NLF_RefCell NLF_SdkModel

theorem erased_subset (s : State) (i n j t : Nat)
    (ht : HasToken ((put s i {s.cells i with readers := (s.cells i).readers.erase n}).cells j) t) :
    HasToken (s.cells j) t := by
  by_cases eq : j=i
  · subst j
    simp only [put_same, HasToken] at ht ⊢
    rcases ht with hw | hr
    · exact Or.inl hw
    · exact Or.inr (List.mem_of_mem_erase hr)
  · simpa [put,eq] using ht

theorem cleared_subset (s : State) (i j t : Nat)
    (ht : HasToken ((put s i {s.cells i with writer := none}).cells j) t) :
    HasToken (s.cells j) t := by
  by_cases eq : j=i
  · subst j
    simp only [put_same, HasToken, reduceCtorEq, false_or] at ht
    exact Or.inr ht
  · simpa [put,eq] using ht

theorem release_preserves (p : Parent) (g : Guard) (h : Invariant p) :
    Invariant (release p g).1 := by
  cases hk : g.kind with
  | shared =>
    by_cases ok : (p.state.cells g.cell).writer = none ∧ g.token ∈ (p.state.cells g.cell).readers
    · have valid := (shared_drop_valid (p.state.cells g.cell) g.token (h.1 g.cell) ok).2
      have eq : NLF_SdkModel.release p.state g =
          .ok (put p.state g.cell {p.state.cells g.cell with readers := (p.state.cells g.cell).readers.erase g.token}) := by
        simp [NLF_SdkModel.release, hk, dropShared,ok.1,ok.2]
      simp only [release,eq]
      exact subset_invariant p.state _ p.next h (put_valid _ _ _ h.1 valid) (erased_subset _ _ _)
    · have eq : NLF_SdkModel.release p.state g = .error .invalidToken := by
        simp [NLF_SdkModel.release,hk,dropShared,ok]
      simpa [release,eq] using h
  | exclusive =>
    by_cases ok : (p.state.cells g.cell).writer = some g.token
    · have valid := (exclusive_drop_valid (p.state.cells g.cell) g.token (h.1 g.cell) ok).2
      have eq : NLF_SdkModel.release p.state g =
          .ok (put p.state g.cell {p.state.cells g.cell with writer := none}) := by
        simp [NLF_SdkModel.release,hk,dropExclusive,ok]
      simp only [release,eq]
      exact subset_invariant p.state _ p.next h (put_valid _ _ _ h.1 valid) (cleared_subset _ _)
    · have eq : NLF_SdkModel.release p.state g = .error .invalidToken := by
        simp [NLF_SdkModel.release,hk,dropExclusive,ok]
      simpa [release,eq] using h

#print axioms erased_subset
#print axioms cleared_subset
#print axioms release_preserves
end NLF_ParentModel
