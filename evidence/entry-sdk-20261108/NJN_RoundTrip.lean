import NJN_GuardComposition
set_option autoImplicit false
namespace NJN_GuardModel
/-- Equality of every carrier component, rather than equality of successful tags. -/
theorem heap_ext (h k : Heap) (ha : h.accounts = k.accounts) (hc : h.cells = k.cells)
    (ht : h.tokens = k.tokens) (hn : h.count = k.count) : h = k := by
  cases h
  cases k
  simp_all
/-- With no intervening operations, a fresh shared token restores the entire heap. -/
theorem shared_roundtrip (h : Heap) (a t : Nat) (fresh : h.tokens t = none)
    (lo : 0 ≤ (h.cells (h.accounts a).cell).counter)
    (hi : (h.cells (h.accounts a).cell).counter < 9223372036854775807) :
    release (acquire h a t false).1 t ⟨(h.accounts a).cell,false⟩ = h := by
  rw [shared_ok h a t lo hi]
  apply heap_ext
  · rfl
  · funext j
    by_cases eq : j = (h.accounts a).cell
    · subst j
      simp [release,replace]
    · simp [release,replace,eq]
  · funext j
    by_cases eq : j = t
    · subst j
      simp [release,replace,fresh]
    · simp [release,replace,eq]
  · rfl
/-- With no intervening writes, an exclusive token restores the entire heap. -/
theorem exclusive_roundtrip (h : Heap) (a t : Nat) (fresh : h.tokens t = none)
    (zero : (h.cells (h.accounts a).cell).counter = 0) :
    release (acquire h a t true).1 t ⟨(h.accounts a).cell,true⟩ = h := by
  rw [exclusive_ok h a t zero]
  apply heap_ext
  · rfl
  · funext j
    by_cases eq : j = (h.accounts a).cell
    · subst j
      simp [release,replace]
      cases hc : h.cells (h.accounts a).cell
      simp_all
    · simp [release,replace,eq]
  · funext j
    by_cases eq : j = t
    · subst j
      simp [release,replace,fresh]
    · simp [release,replace,eq]
  · rfl
#print axioms heap_ext
#print axioms shared_roundtrip
#print axioms exclusive_roundtrip
end NJN_GuardModel
