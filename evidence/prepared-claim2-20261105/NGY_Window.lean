import NGU_Part006
import NCI_KMXFrames
set_option autoImplicit false
namespace AspisR1.NGY_Window

/-- One selected physical 32-byte input window, not a whole-buffer copy. -/
theorem selected {A : Type} (src dst : Nat → A) (lane byte : Nat) (h : byte<32) :
 KMX_CopyMeaning.loop (fun i => src (32*lane+i)) dst 0 32 byte=src (32*lane+byte) := by
 rw [NCI_KMXFrames.window]
 exact if_pos h

theorem bounded (lane byte : Nat) (hl : lane<29) (hb : byte<32) :
 32*lane+byte<928 := by omega

/-- The same arbitrary outside state is retained; no zero-filled suffix is used. -/
theorem frame {A : Type} (src dst : Nat → A) (lane k : Nat)
 (outside : k<32*lane ∨ 32*lane+32≤k) :
 KMX_CopyMeaning.loop src dst (32*lane) 32 k=dst k :=
 KMX_CopyMeaning.copy_frame src dst (32*lane) 32 k outside

/-- Different selected lanes have disjoint windows and commute at the value level. -/
theorem disjoint {A : Type} (src1 src2 dst : Nat → A) (a b k : Nat) (h : a<b) :
 KMX_CopyMeaning.loop src2 (KMX_CopyMeaning.loop src1 dst (32*a) 32) (32*b) 32 k=
 KMX_CopyMeaning.loop src1 (KMX_CopyMeaning.loop src2 dst (32*b) 32) (32*a) 32 k := by
 apply NCI_KMXFrames.disjoint
 left
 omega

#print axioms selected
#print axioms bounded
#print axioms frame
#print axioms disjoint
end AspisR1.NGY_Window
