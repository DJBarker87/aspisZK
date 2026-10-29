import R1Z.PV_OWND_CounterBranch
set_option autoImplicit false
namespace R1Z.PV_OWND_CounterBounds
open PV_OWND_EndpointCounter

theorem post_bound (counts next : Counts) (row : UInt16)
 (h:bump counts row=.ok next) (old:∀ i, counts i≤2) : ∀ i, next i≤2 := by
 unfold bump at h
 split at h
 · cases h
 · cases h
   intro i
   change (if i=row.toNat then counts i+1 else counts i)≤2
   split
   · rename_i eq
     subst i
     have bound:=old row.toNat
     omega
   · exact old i

theorem byte_room (counts next : Counts) (row : UInt16)
 (h:bump counts row=.ok next) : next row.toNat≤2 := by
 unfold bump at h
 split at h
 · cases h
 · rename_i room
   cases h
   simp only [ite_true]
   omega
#print axioms post_bound
#print axioms byte_room
end R1Z.PV_OWND_CounterBounds
