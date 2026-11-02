import KMX_CopyMeaning
import Aeneas
set_option autoImplicit false
namespace NEO_WindowFrame
open Aeneas Aeneas.Std Result

/-- Source and destination addresses are separate affine windows. This is the
value/frame composition for the exact approved KMX indexed copy, not a claim
that pointer validity or allocation identity follows from value equality. -/
def relocated {T : Type} (src dst : Nat → T) (source target width : Nat) : Nat → T :=
 KMX_CopyMeaning.loop (fun k => src (source+(k-target))) dst target width

theorem selected {T : Type} (src dst : Nat → T) (source target width j : Nat)
 (inside : j < width) : relocated src dst source target width (target+j)=src (source+j) := by
 rw [relocated,KMX_CopyMeaning.loop_spec,if_pos (by omega)]
 congr 1
 omega

theorem outside {T : Type} (src dst : Nat → T) (source target width k : Nat)
 (apart : k < target ∨ target+width ≤ k) :
 relocated src dst source target width k=dst k :=
 KMX_CopyMeaning.copy_frame _ _ _ _ _ apart

/-- Unrelated allocation cells can be arbitrary. Equal selected source bytes
produce the same copied window even at different source/destination offsets. -/
theorem rebase {T : Type} (a b da db : Nat → T) (oa ob ta tb width : Nat)
 (same : ∀ j, j < width → a (oa+j)=b (ob+j)) (j : Nat) (inside : j < width) :
 relocated a da oa ta width (ta+j)=relocated b db ob tb width (tb+j) := by
 rw [selected _ _ _ _ _ _ inside,selected _ _ _ _ _ _ inside]
 exact same j inside

/-- Exact checked slice relocation for arbitrary backing length. -/
def segment (bytes : Slice U8) (offset width : Nat) (bound : offset+width ≤ bytes.val.length) :
 List U8 := (bytes.val.drop offset).take width

theorem length (bytes : Slice U8) (offset width : Nat) (bound : offset+width ≤ bytes.val.length) :
 (segment bytes offset width bound).length=width := by
 simp only [segment,List.length_take,List.length_drop]
 omega

theorem subwindow (bytes : Slice U8) (offset width start count : Nat)
 (bound : offset+width ≤ bytes.val.length) (inner : start+count ≤ width) :
 ((segment bytes offset width bound).drop start).take count =
 (bytes.val.drop (offset+start)).take count := by
 simp only [segment,List.drop_take,List.drop_drop,List.take_take]
 congr 1
 omega

#print axioms selected
#print axioms outside
#print axioms rebase
#print axioms length
#print axioms subwindow
end NEO_WindowFrame
