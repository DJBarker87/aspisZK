import NIT_ArrayFrames
import NIT_Cuts
set_option autoImplicit false
namespace AspisR1.NJF_WindowPartitions
open Aeneas Aeneas.Std Result NIT_Cuts

/-- Exhaustive observation-selector partition, not a business-input condition. -/
theorem slots {P : Nat → Prop} (low : ∀ i,i<3 → P i)
 (high : ∀ i,3 ≤ i → i<7 → P i) : ∀ i,i<7 → P i := by
 intro i hi
 by_cases small : i<3
 · exact low i small
 · exact high i (by omega) hi

theorem powers {P : Nat → Prop} (low : ∀ i,i<2 → P i)
 (high : ∀ i,2 ≤ i → i<4 → P i) : ∀ i,i<4 → P i := by
 intro i hi
 by_cases small : i<2
 · exact low i small
 · exact high i (by omega) hi

/-- Full Parts equality follows from the two disjoint native slot windows. -/
theorem parts (before after : Parts)
 (low : ∀ i,i<3 → epick before i=epick after i)
 (high : ∀ i,3 ≤ i → i<7 → epick before i=epick after i) : before=after := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 exact slots low high

/-- The two two-word power-index windows similarly cover the complete array. -/
theorem partials (before after : Powers)
 (low : ∀ i,i<2 → epick before i=epick after i)
 (high : ∀ i,2 ≤ i → i<4 → epick before i=epick after i) : before=after := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 exact powers low high

#print axioms slots
#print axioms powers
#print axioms parts
#print axioms partials
end AspisR1.NJF_WindowPartitions
