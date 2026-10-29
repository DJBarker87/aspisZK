import Aeneas
namespace R1Z.PV_RDB2E_PointerOffsets
set_option autoImplicit false
/-- Mathematical byte addresses only. No provenance/aliasing premise is hidden here. -/
def address (base index : Nat) : Nat := base + 4*index

theorem injective (base i j : Nat) : address base i=address base j ↔ i=j := by
  unfold address; omega

theorem unequal (base i j : Nat) (h : i≠j) : address base i≠address base j := by
  intro e; exact h ((injective base i j).mp e)

theorem next (base i : Nat) : address base i+4=address base (i+1) := by
  unfold address; omega

theorem previous (base j : Nat) (h : 0<j) : address base j-4=address base (j-1) := by
  unfold address; omega

theorem eight_bounds (base i : Nat) (h : i<8) :
    base≤address base i ∧ address base i+4≤address base 8 := by
  unfold address; omega

theorem past_end (base : Nat) : address base 8=base+32 := rfl

theorem nonempty (base front back : Nat) (h : front≤back) :
    address base front≠address base back ↔ front<back := by
  rw [ne_eq,injective]; omega

theorem no_wrap (limit base : Nat) (space : base+32≤limit) (i : Nat) (h : i≤8) :
    address base i≤limit := by unfold address; omega

#print axioms injective
#print axioms unequal
#print axioms next
#print axioms previous
#print axioms eight_bounds
#print axioms past_end
#print axioms nonempty
#print axioms no_wrap
end R1Z.PV_RDB2E_PointerOffsets
