import R1AppendReconstruct

/-! A finite indexed sequence of parent transitions folds to the result of
`reconstructFrom`. The parent and recursive empty-root operations remain
abstract. -/
set_option autoImplicit false

namespace AspisPool.IncrementalMerkleV1

theorem reconstruct_ofFn_chain {α : Type}
    (parent : α → α → α) (emptyLeaf : α) (n level : Nat)
    (y : Nat → α) (slots : Fin n → Option α)
    (h : ∀ i : Fin n,
      y (i.val + 1) =
        match slots i with
        | none => parent (y i.val)
            (recursiveEmptyRoot parent emptyLeaf (level + i.val))
        | some left => parent left (y i.val)) :
    reconstructFrom parent emptyLeaf level (y 0) (List.ofFn slots) = y n := by
  induction n generalizing level y with
  | zero => simp only [List.ofFn_zero, reconstructFrom]
  | succ n ih =>
      rw [List.ofFn_succ]
      cases hs : slots 0 with
      | none =>
          have h0 : y 1 = parent (y 0)
              (recursiveEmptyRoot parent emptyLeaf level) := by
            simpa [hs] using h 0
          simp only [reconstructFrom]
          rw [← h0]
          let y' : Nat → α := fun j => y (j + 1)
          let slots' : Fin n → Option α := fun i => slots i.succ
          have htail : ∀ i : Fin n,
              y' (i.val + 1) =
                match slots' i with
                | none => parent (y' i.val)
                    (recursiveEmptyRoot parent emptyLeaf (level + 1 + i.val))
                | some left => parent left (y' i.val) := by
            intro i
            have hi := h i.succ
            have hlevel : level + 1 + i.val = level + i.succ.val := by
              simp only [Fin.val_succ]
              omega
            rw [hlevel]
            simpa only [y', slots', Fin.val_succ, Nat.add_assoc] using hi
          simpa [y'] using ih (level + 1) y' slots' htail
      | some left =>
          have h0 : y 1 = parent left (y 0) := by
            simpa [hs] using h 0
          simp only [reconstructFrom]
          rw [← h0]
          let y' : Nat → α := fun j => y (j + 1)
          let slots' : Fin n → Option α := fun i => slots i.succ
          have htail : ∀ i : Fin n,
              y' (i.val + 1) =
                match slots' i with
                | none => parent (y' i.val)
                    (recursiveEmptyRoot parent emptyLeaf (level + 1 + i.val))
                | some tailLeft => parent tailLeft (y' i.val) := by
            intro i
            have hi := h i.succ
            have hlevel : level + 1 + i.val = level + i.succ.val := by
              simp only [Fin.val_succ]
              omega
            rw [hlevel]
            simpa only [y', slots', Fin.val_succ, Nat.add_assoc] using hi
          simpa [y'] using ih (level + 1) y' slots' htail

#print axioms reconstruct_ofFn_chain

end AspisPool.IncrementalMerkleV1
