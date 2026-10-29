import Init.Omega
set_option autoImplicit false
namespace R1Z.PV_OWNH_Address
/-- A pointer inside a live, nonwrapping allocation, in element coordinates. -/
def at (base offset : Nat) : Nat := base + offset

theorem same_allocation_eq (base i j : Nat) :
    at base i = at base j ↔ i = j := Nat.add_left_cancel_iff

theorem same_allocation_lt (base i j : Nat) :
    at base i < at base j ↔ i < j := Nat.add_lt_add_iff_left

theorem same_allocation_le (base i j : Nat) :
    at base i ≤ at base j ↔ i ≤ j := Nat.add_le_add_iff_left

theorem cursor_distance (base i j : Nat) :
    at base j - at base i = j - i := Nat.add_sub_add_left _ _ _

theorem rebase_equality (a b i j : Nat) :
    (at a i = at a j) ↔ (at b i = at b j) := by
  rw [same_allocation_eq, same_allocation_eq]

theorem rebase_order (a b i j : Nat) :
    (at a i < at a j) ↔ (at b i < at b j) := by
  rw [same_allocation_lt, same_allocation_lt]

theorem rebase_distance (a b i j : Nat) :
    at a j - at a i = at b j - at b i := by
  rw [cursor_distance, cursor_distance]

theorem block_bound (r : Nat) (h : r < 1024) : r / 16 < 64 := by omega

theorem shift_bound (r : Nat) : r % 16 < 16 := Nat.mod_lt _ (by omega)

/-- No allocator-process-state component is inspected by an owned-data read. -/
theorem no_state_channel {Owned State Value : Type} (read : Owned → Value)
    (memory : Owned) (before after : State) :
    (fun (x : Owned × State) => read x.1) (memory,before) =
      (fun (x : Owned × State) => read x.1) (memory,after) := rfl

#print axioms same_allocation_eq
#print axioms same_allocation_lt
#print axioms same_allocation_le
#print axioms cursor_distance
#print axioms rebase_equality
#print axioms rebase_order
#print axioms rebase_distance
#print axioms block_bound
#print axioms shift_bound
#print axioms no_state_channel
end R1Z.PV_OWNH_Address
