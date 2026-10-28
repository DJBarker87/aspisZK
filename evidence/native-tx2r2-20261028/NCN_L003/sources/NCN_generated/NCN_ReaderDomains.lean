import NCI_ReaderLayout
import NCI_ReaderWindows
import NCI_ResidueBounds
set_option autoImplicit false
namespace AspisR1.NCN_ReaderDomains

def Raw32Cursor (start : Nat) : Prop :=
  (∃ i < 7, start = 80+32*i) ∨ (∃ i < 2, start = 632+32*i)

theorem prefix_bound (i : Nat) (hi : i < 7) :
    Raw32Cursor (80+32*i) ∧ 80+32*i+32 ≤ 1768 :=
  ⟨Or.inl ⟨i,hi,rfl⟩,by omega⟩

theorem tail_bound (i : Nat) (hi : i < 2) :
    Raw32Cursor (632+32*i) ∧ 632+32*i+32 ≤ 1768 :=
  ⟨Or.inr ⟨i,hi,rfl⟩,by omega⟩

/-- These nine positions are exactly the frozen resume's raw32 calls: state,
roots, gamma/kappa/alphas, then claim/rhs. This is a domain cover, not a native
caller execution theorem. -/
theorem source_positions (start : Nat)
    (h : start ∈ ([80,112,144,176,208,240,272,632,664] : List Nat)) :
    Raw32Cursor start := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h <;> subst start
  · exact (prefix_bound 0 (by decide)).1
  · exact (prefix_bound 1 (by decide)).1
  · exact (prefix_bound 2 (by decide)).1
  · exact (prefix_bound 3 (by decide)).1
  · exact (prefix_bound 4 (by decide)).1
  · exact (prefix_bound 5 (by decide)).1
  · exact (prefix_bound 6 (by decide)).1
  · exact (tail_bound 0 (by decide)).1
  · exact (tail_bound 1 (by decide)).1

/-- The arbitrary product/add precondition of the split native window follows
from the existing query-cadence invariant, without restricting any caller. -/
theorem word_add_domain (raw product terms : Nat)
    (hr : raw < NCI_ResidueBounds.Boundary + (terms%4)*NCI_ResidueBounds.MaxProduct)
    (hp : product ≤ NCI_ResidueBounds.MaxProduct) :
    raw ≤ 18446744073709551615-product := by
  have h := NCI_ResidueBounds.group_nowrap raw product (terms%4)
    (Nat.mod_lt _ (by decide)) hr hp
  omega

#print axioms prefix_bound
#print axioms tail_bound
#print axioms source_positions
#print axioms word_add_domain
end AspisR1.NCN_ReaderDomains
