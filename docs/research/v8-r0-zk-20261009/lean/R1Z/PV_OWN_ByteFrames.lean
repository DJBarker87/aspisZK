import R1Z.PV_OWN_Bytes
set_option autoImplicit false
namespace R1Z.PV_OWN_ByteFrames
open PV_OWN_Bytes
/-- Disjoint typed writes commute, at their actual byte ranges. -/
theorem commute (old a b : Bytes) (s n t m : Nat) (disjoint:s+n≤t ∨ t+m≤s) :
 overwrite (overwrite old s n a) t m b=overwrite (overwrite old t m b) s n a := by
 funext i
 by_cases hs:s≤i ∧ i<s+n
 · have ht:¬(t≤i ∧ i<t+m) := by omega
   simp [overwrite,hs,ht]
 · simp [overwrite,hs]
/-- No read/write proof can fabricate a byte outside the allocation. -/
theorem fits_subrange (size start width i : Nat) (fits:start+width≤size) (hi:i<width) :
 start+i<size := by omega
#print axioms commute
#print axioms fits_subrange
end R1Z.PV_OWN_ByteFrames
