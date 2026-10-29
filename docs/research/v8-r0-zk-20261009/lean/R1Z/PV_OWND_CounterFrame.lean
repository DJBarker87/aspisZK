import R1Z.PV_OWND_CounterBranch
set_option autoImplicit false
namespace R1Z.PV_OWND_CounterFrame
open PV_OWND_EndpointCounter

theorem other (counts next : Counts) (row : UInt16) (i : Nat)
 (h:bump counts row=.ok next) (hne:i≠row.toNat) : next i=counts i := by
 unfold bump at h
 split at h
 · cases h
 · cases h
   simp only [hne,ite_false]

theorem changed (counts next : Counts) (row : UInt16)
 (h:bump counts row=.ok next) : next row.toNat=counts row.toNat+1 := by
 unfold bump at h
 split at h
 · cases h
 · cases h
   simp only [ite_true]
#print axioms other
#print axioms changed
end R1Z.PV_OWND_CounterFrame
