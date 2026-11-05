import NHW_ModelWriter
set_option autoImplicit false
namespace AspisR1.NHW_CopyFrame
/-- The one native arbitrary-byte window composes over all32 output positions
using the exact KMX copy value law. Background bytes are unrestricted. -/
theorem folded {A : Type} (source destination : Nat → A) (j : Nat) (inside : j<32) :
 KMX_CopyMeaning.loop (fun i=>source (7751+i)) destination 0 32 j=source (7751+j) := by
 rw [KMX_CopyMeaning.copy_prefix,if_pos inside]

theorem frame {A : Type} (source destination : Nat → A) (j : Nat) (outside : 32≤j) :
 KMX_CopyMeaning.loop (fun i=>source (7751+i)) destination 0 32 j=destination j :=
 KMX_CopyMeaning.copy_frame _ _ 0 32 j (Or.inr outside)

theorem source_range : 7751+32=7783 ∧ 7783≤57607 := by decide
#print axioms folded
#print axioms frame
#print axioms source_range
end AspisR1.NHW_CopyFrame
