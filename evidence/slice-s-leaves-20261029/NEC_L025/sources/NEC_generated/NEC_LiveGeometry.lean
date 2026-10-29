import Aeneas
set_option autoImplicit false
namespace NEC_LiveGeometry
open Aeneas Aeneas.Std

/-- The selected native digest call is current_root at slot0, then twenty
frontier digests. This is input geometry, not a stand-in decoder. -/
def start (slot : Nat) : Nat := 128+32*slot

theorem current_root : start 0=128 := rfl

theorem frontier_start (level : Nat) : start (level+1)=160+32*level := by
 unfold start
 omega

theorem byte_in_bounds (slot byte : Nat) (slotBound : slot<21) (byteBound : byte<32) :
 start slot+byte<800 := by
 unfold start
 omega

theorem window_length (bytes : List U8) (length : bytes.length=800)
 (slot : Nat) (slotBound : slot<21) :
 ((bytes.drop (start slot)).take 32).length=32 := by
 simp only [List.length_take,List.length_drop,length]
 unfold start
 omega

theorem disjoint (left right : Nat) (ordered : left<right) :
 start left+32≤start right := by
 unfold start
 omega

theorem same_slot (left right : Nat) (same : start left=start right) : left=right := by
 unfold start at same
 omega

/-- The scalar header and digest input regions are disjoint. -/
theorem header_frame (slot : Nat) : 128≤start slot := by
 unfold start
 omega

#print axioms current_root
#print axioms frontier_start
#print axioms byte_in_bounds
#print axioms window_length
#print axioms disjoint
#print axioms same_slot
#print axioms header_frame
end NEC_LiveGeometry
