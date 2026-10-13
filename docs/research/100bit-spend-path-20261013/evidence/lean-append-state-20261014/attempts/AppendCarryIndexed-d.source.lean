import AspisFormal.Pool.IncrementalMerkleV1

set_option autoImplicit false

namespace AspisPool.IncrementalMerkleV1

/-- An indexed list of occupied slots below `c`, followed by the first empty
slot, carries the prefix into level `c` and leaves higher slots unchanged. -/
theorem appendCarry_indexed_more {α : Type} (parent : α → α → α)
    {n c : Nat} (hc : c ≤ n) (hcn : c < n)
    (slots : Fin n → Option α) (y : Nat → α)
    (hbelow : ∀ i : Fin n, i.val < c →
      ∃ left, slots i = some left ∧ y (i.val + 1) = parent left (y i.val))
    (hstop : ∀ h : c < n, slots ⟨c, h⟩ = none) :
    appendCarry parent (y 0) (List.ofFn slots) = .more
      (List.ofFn (fun i : Fin n =>
        if i.val < c then none else if i.val = c then some (y c) else slots i)) := by
  induction n generalizing c y with
  | zero => omega
  | succ n ih =>
      cases c with
      | zero =>
          have hzero : slots 0 = none := by simpa using hstop (by omega)
          simp [appendCarry, List.ofFn_succ, hzero]
      | succ c =>
          have hhead := hbelow ⟨0, by omega⟩ (by omega)
          obtain ⟨left, hleft, hy⟩ := hhead
          change slots 0 = some left at hleft
          have hy1 : y 1 = parent left (y 0) := by simpa using hy
          let tailSlots : Fin n → Option α := fun i => slots i.succ
          let tailY : Nat → α := fun i => y (i + 1)
          have hbelow' : ∀ i : Fin n, i.val < c →
              ∃ left, tailSlots i = some left ∧
                tailY (i.val + 1) = parent left (tailY i.val) := by
            intro i hi
            have hidx : (i.succ : Fin (n + 1)).val < c + 1 := by change i.val + 1 < c + 1; omega
            obtain ⟨left', hleft', hy'⟩ := hbelow i.succ hidx
            refine ⟨left', hleft', ?_⟩
            simpa [tailY, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy'
          have hstop' : ∀ h : c < n, tailSlots ⟨c, h⟩ = none := by
            intro h
            have hs := hstop (by omega : c + 1 < n + 1)
            simpa [tailSlots] using hs
          have hc' : c ≤ n := by omega
          have hcn' : c < n := by omega
          have hrec := ih hc' hcn' tailSlots tailY hbelow' hstop'
          have happend : appendCarry parent (y 1) (List.ofFn tailSlots) = .more
              (List.ofFn (fun i : Fin n =>
                if i.val < c then none else if i.val = c then some (y (c + 1))
                else tailSlots i)) := by
            simpa [tailY] using hrec
          rw [List.ofFn_succ]
          rw [← hy1]
          simp only [appendCarry, hleft]
          rw [happend]
          simp [tailSlots]

/-- If every indexed slot is occupied, the carry exits the frontier as the
root at level `n`. -/
theorem appendCarry_indexed_full {α : Type} (parent : α → α → α)
    {n c : Nat} (hc : c ≤ n) (hcn : c = n)
    (slots : Fin n → Option α) (y : Nat → α)
    (hbelow : ∀ i : Fin n, i.val < c →
      ∃ left, slots i = some left ∧ y (i.val + 1) = parent left (y i.val))
    (hstop : ∀ h : c < n, slots ⟨c, h⟩ = none) :
    appendCarry parent (y 0) (List.ofFn slots) = .full (y n) := by
  subst c
  induction n generalizing y with
  | zero => simp [appendCarry, List.ofFn]
  | succ n ih =>
      have hhead := hbelow ⟨0, by omega⟩ (by omega)
      obtain ⟨left, hleft, hy⟩ := hhead
      change slots 0 = some left at hleft
      have hy1 : y 1 = parent left (y 0) := by simpa using hy
      let tailSlots : Fin n → Option α := fun i => slots i.succ
      let tailY : Nat → α := fun i => y (i + 1)
      have hbelow' : ∀ i : Fin n, i.val < n →
          ∃ left, tailSlots i = some left ∧
            tailY (i.val + 1) = parent left (tailY i.val) := by
        intro i hi
        have hidx : (i.succ : Fin (n + 1)).val < n + 1 := by change i.val + 1 < n + 1; omega
        obtain ⟨left', hleft', hy'⟩ := hbelow i.succ hidx
        refine ⟨left', hleft', ?_⟩
        simpa [tailY, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hy'
      have hstop' : ∀ h : n < n, tailSlots ⟨n, h⟩ = none := by
        intro h
        exact (Nat.lt_irrefl n h).elim
      have hrec := ih tailSlots tailY (Nat.le_refl n) hbelow' hstop'
      have happend : appendCarry parent (y 1) (List.ofFn tailSlots) = .full (y (n + 1)) := by
        simpa [tailY] using hrec
      rw [List.ofFn_succ]
      rw [← hy1]
      simp only [appendCarry, hleft]
      rw [happend]
      simp [tailSlots]

#print axioms appendCarry_indexed_more
#print axioms appendCarry_indexed_full

end AspisPool.IncrementalMerkleV1
