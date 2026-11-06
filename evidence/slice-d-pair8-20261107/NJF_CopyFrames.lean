import KMX_CopyMeaning
import NIT_ArrayFrames
set_option autoImplicit false
namespace AspisR1.NJF_CopyFrames

/-- Logical raw-word state: scratch has 64*4 words, Parts has 7*8 words.
Physical borrow validity/nonaliasing remains the existing Rust/P6 domain; these
are value coordinates, not addresses or a new allocation premise. -/
def scratchWords : Nat := 256
def partsWords : Nat := 56

def applyWindows {T : Type} (scratch parts before : Nat → T) : Nat → T :=
 KMX_CopyMeaning.loop parts (KMX_CopyMeaning.loop scratch before 0 scratchWords) scratchWords partsWords

/-- A selected scratch word is unchanged by the disjoint Parts window. -/
theorem scratch_frame {T : Type} (scratch parts before : Nat → T) (i : Nat)
 (small : i<scratchWords) : applyWindows scratch parts before i=scratch i := by
 unfold applyWindows
 rw [KMX_CopyMeaning.copy_frame _ _ _ _ _ (Or.inl small),KMX_CopyMeaning.copy_prefix,if_pos small]

/-- Every selected Parts word is the Parts oracle reply; no entire large copy
is normalized. This composes the native arbitrary-offset windows symbolically. -/
theorem parts_value {T : Type} (scratch parts before : Nat → T) (i : Nat)
 (small : i<partsWords) : applyWindows scratch parts before (scratchWords+i)=parts (scratchWords+i) := by
 unfold applyWindows
 rw [KMX_CopyMeaning.loop_spec]
 apply if_pos
 constructor <;> omega

/-- All coordinates outside both declared footprints retain their pre-state. -/
theorem outside_frame {T : Type} (scratch parts before : Nat → T) (i : Nat)
 (outside : scratchWords + partsWords ≤ i) : applyWindows scratch parts before i=before i := by
 unfold applyWindows
 rw [KMX_CopyMeaning.copy_frame _ _ _ _ _ (Or.inr outside)]
 apply KMX_CopyMeaning.copy_frame
 right
 omega

#print KMX_CopyMeaning.loop
#print axioms scratch_frame
#print axioms parts_value
#print axioms outside_frame
end AspisR1.NJF_CopyFrames
