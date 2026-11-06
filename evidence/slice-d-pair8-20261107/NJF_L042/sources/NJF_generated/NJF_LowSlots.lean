import NJF_WindowPartitions
set_option autoImplicit false
namespace AspisR1.NJF_LowSlots
open Aeneas Aeneas.Std Result NIT_Cuts

/-- Exhaustive literal refinement of the timed-out low observation region.
No restriction is added to parent inputs or child reply/mutation values. -/
theorem low {P : Nat → Prop} (zero : P 0) (one : P 1) (two : P 2) : ∀ i,i<3 → P i := by
 intro i hi
 rcases (show i=0 ∨ i=1 ∨ i=2 by omega) with h|h|h
 all_goals subst i;assumption

theorem complete {P : Nat → Prop} (zero : P 0) (one : P 1) (two : P 2)
 (high : ∀ i,3 ≤ i → i<7 → P i) : ∀ i,i<7 → P i :=
 NJF_WindowPartitions.slots (low zero one two) high

/-- Native raw-word windows at slots0/1/2 and the admitted 3..6 region identify
all seven Parts cells, with the same selector-independent decoded snapshot. -/
theorem parts (before after : Parts)
 (zero : epick before 0=epick after 0) (one : epick before 1=epick after 1)
 (two : epick before 2=epick after 2)
 (high : ∀ i,3 ≤ i → i<7 → epick before i=epick after i) : before=after := by
 apply NIT_ArrayFrames.ext NHI_Scalar.zero
 exact complete zero one two high

#print axioms low
#print axioms complete
#print axioms parts
end AspisR1.NJF_LowSlots
