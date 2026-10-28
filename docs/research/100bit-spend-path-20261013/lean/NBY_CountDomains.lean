import NBV_Audit
import MultiproofConeCountBounds

set_option autoImplicit false
namespace AspisR1.NBY_CountDomains

/-- Reached row accumulators satisfy the native finite-word gate; this is
stronger than merely bounding the final eighteen-level answer. -/
theorem row_domain (depth n i count : Nat) (height : depth < 18)
    (size : n ≤ 16) (active : i < n) (spent : count ≤ 16*depth+i) :
    count ≤ 288 ∧ count+2 < 18446744073709551616 := by omega

/-- The same consumed-prefix invariant advances with a one/two-child group. -/
theorem row_preserves (depth i j count : Nat) (width : 1 ≤ j-i ∧ j-i ≤ 2)
    (advances : i < j) (spent : count ≤ 16*depth+i) :
    count+(2-(j-i)) ≤ 16*depth+j := by omega

/-- End-of-level control resets i on the actual next level. -/
theorem level_preserves (depth n count : Nat) (size : n ≤ 16)
    (spent : count ≤ 16*depth+n) : count ≤ 16*(depth+1) := by omega

/-- Import the constructed initialized carrier and existing complete count
bound, rather than re-proving either recurrence. -/
theorem initialized_bound (key : Nat → Nat) (n : Nat) (size : n ≤ 16)
    (ordered : (MultiproofConeCountPhysical.cells key 0 n).Pairwise (·<·)) :
    NBJ_CountLevels.nativeCount 18 (NBV_CountInitialization.initialized key n) n ≤ 288 := by
  rw [NBV_CountInitialization.count_initialized key n ordered]
  apply MultiproofConeCountBounds.eighteen_bound
  · simpa only [MultiproofConeCountPhysical.cells,List.length_map,List.length_range] using size
  · exact ordered

#print axioms row_domain
#print axioms row_preserves
#print axioms level_preserves
#print axioms initialized_bound
end AspisR1.NBY_CountDomains
