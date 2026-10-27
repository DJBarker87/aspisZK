import R1Z.PV_CB3_TransportOrder
set_option autoImplicit false
namespace R1Z.PV_CB3_TransportMembership
open PV_CB3_TransportOrder

theorem member_iff (pivot : Nat) (pads : List Nat)
    (hp : ∀ r, r ∈ pads → r < pivot) (r : Nat) : r ∈ order pivot pads ↔ r ≤ pivot := by
  constructor
  · exact member_bound pivot pads hp r
  · intro hr
    by_cases he : r=pivot
    · subst r; exact pivot_mem pivot pads
    · by_cases hm : r ∈ pads
      · exact pads_mem pivot pads r hm
      · have hl : r < pivot := by omega
        simp only [order,List.mem_append]
        apply Or.inl
        apply Or.inr
        simp only [List.mem_filter,List.mem_range]
        exact ⟨hl,by simpa using hm⟩

theorem range_membership (pivot : Nat) (pads : List Nat)
    (hp : ∀ r, r ∈ pads → r < pivot) (r : Nat) :
    r ∈ order pivot pads ↔ r ∈ List.range (pivot+1) := by
  rw [member_iff pivot pads hp,List.mem_range]
  omega
#print axioms member_iff
#print axioms range_membership
end R1Z.PV_CB3_TransportMembership
