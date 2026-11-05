import NHV_COMBINED_IMPORT
set_option autoImplicit false
namespace NID_RawWindowFrame
open Aeneas Aeneas.Std

def limb (row : Array U64 4#usize) (j : Fin 4) : U64 :=
 row.val[j.val]'(by rw [row.property];exact j.isLt)

/-- Four disjoint one-word windows reconstruct the entire SAME raw row. -/
theorem row (before after : Array U64 4#usize)
 (w0 : limb before 0=limb after 0) (w1 : limb before 1=limb after 1)
 (w2 : limb before 2=limb after 2) (w3 : limb before 3=limb after 3) :
 before=after := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact before.property.trans after.property.symm
 · intro i hi hj
   have bound : i<4 := by rw [before.property] at hi;exact hi
   rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl | rfl
   · exact w0
   · exact w1
   · exact w2
   · exact w3

/-- Quantification over arbitrary row offsets lifts the contiguous one-word
cuts without fixing other rows, metadata, proof bytes or Prepared fields. -/
theorem rows (before after : List (Array U64 4#usize)) (size : before.length=after.length)
 (windows : ∀ i (hi : i<before.length) (hj : i<after.length) (j : Fin 4),
  limb (before[i]'hi) j=limb (after[i]'hj) j) : before=after := by
 apply List.ext_getElem size
 intro i hi hj
 exact row _ _ (windows i hi hj 0) (windows i hi hj 1)
  (windows i hi hj 2) (windows i hi hj 3)

/-- These windows are consecutive and do not overlap. Width is bytes per
u64 word in the retained Rust/ABI interpretation, not a new endian assumption. -/
theorem contiguous (j : Nat) (inside : j<4) :
 8*j+8≤32 ∧ (j<3 → 8*j+8=8*(j+1)) := by omega
#print axioms row
#print axioms rows
#print axioms contiguous
end NID_RawWindowFrame
