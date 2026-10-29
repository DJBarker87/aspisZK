import R1Z.PV_OWND_EndpointCounter
set_option autoImplicit false
namespace R1Z.PV_OWND_CounterBranch
open PV_OWND_EndpointCounter

theorem range_error (counts : Counts) (row : UInt16) (h:1024≤row.toNat) :
 bump counts row=.error (.endpointCapacity row) := by
 simp only [bump,show row.toNat≥1024 ∨ counts row.toNat≥2 from Or.inl h,ite_true]

theorem capacity_error (counts : Counts) (row : UInt16) (h:2≤counts row.toNat) :
 bump counts row=.error (.endpointCapacity row) := by
 simp only [bump,show row.toNat≥1024 ∨ counts row.toNat≥2 from Or.inr h,ite_true]

theorem success (counts : Counts) (row : UInt16) (range:row.toNat<1024)
 (room:counts row.toNat<2) :
 bump counts row=.ok (fun i=>if i=row.toNat then counts i+1 else counts i) := by
 simp only [bump,show ¬(row.toNat≥1024 ∨ counts row.toNat≥2) by omega,ite_false]
#print axioms range_error
#print axioms capacity_error
#print axioms success
end R1Z.PV_OWND_CounterBranch
