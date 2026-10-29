import R1Z.PV_OWNB_PaddingStore
set_option autoImplicit false
namespace R1Z.PV_OWNB_RegionFrame
open PV_OWN_Heap PV_OWN_Bytes PV_OWNB_Padding PV_OWNB_PaddingStore
 theorem disjoint (required value : Bytes) (c : Cell) (s n t m : Nat)
 (h:Represents required n c s) (bound:∀ i b, required i=some b → i<n)
 (apart:s+n≤t ∨ t+m≤s) : Represents required n (store c t m value) s := by
 refine ⟨h.1,?_⟩
 intro i b hi
 have hh:=bound i b hi
 change overwrite c.contents t m value (s+i)=some b
 rw [outside _ _ _ _ _ (by omega)]
 exact h.2 i b hi
#print axioms disjoint
end R1Z.PV_OWNB_RegionFrame
