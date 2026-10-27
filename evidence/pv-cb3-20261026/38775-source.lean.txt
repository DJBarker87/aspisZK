import Std
set_option autoImplicit false
namespace R1Z.PV_CB3_TransportOrder
/-- Symbolic shape of the const order builder: asserted pad rows, unused rows,
then the pivot. No 1024-entry array is normalized. -/
def order (pivot : Nat) (pads : List Nat) : List Nat :=
  (pads ++ (List.range pivot).filter (fun r => !(pads.contains r))) ++ [pivot]

theorem member_bound (pivot : Nat) (pads : List Nat)
    (hp : ∀ r, r ∈ pads → r < pivot) (r : Nat) (hr : r ∈ order pivot pads) :
    r ≤ pivot := by
  simp only [order,List.mem_append,List.mem_filter,List.mem_range,List.mem_cons,List.not_mem_nil,
    or_false] at hr
  rcases hr with (hr|⟨hr,_⟩)|hr
  · exact Nat.le_of_lt (hp r hr)
  · exact Nat.le_of_lt hr
  · omega

theorem semantic_row_bound (pads : List Nat) (hp : ∀ r, r ∈ pads → r < 1023)
    (r : Nat) (hr : r ∈ order 1023 pads) : r < 1024 := by
  have h := member_bound 1023 pads hp r hr
  omega

theorem pivot_mem (pivot : Nat) (pads : List Nat) : pivot ∈ order pivot pads := by
  simp [order]

theorem pads_mem (pivot : Nat) (pads : List Nat) (r : Nat) (hr : r ∈ pads) :
    r ∈ order pivot pads := by simp only [order,List.mem_append]; exact Or.inl (Or.inl hr)
#print axioms member_bound
#print axioms semantic_row_bound
#print axioms pivot_mem
#print axioms pads_mem
end R1Z.PV_CB3_TransportOrder
