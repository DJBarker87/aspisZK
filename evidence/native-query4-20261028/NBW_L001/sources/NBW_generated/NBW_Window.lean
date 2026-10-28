import KMX_CopyMeaning
import NBO_Audit
set_option autoImplicit false
namespace NBW_Window
/-- Compose adjacent windows on the same retained source. No allocation,
pointer, canonicality, or source-to-model premise is hidden here. -/
theorem adjacent {α : Type} (src dst : Nat → α) (start left right : Nat) :
 KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst start left)
   (start+left) right = KMX_CopyMeaning.loop src dst start (left+right) := by
 funext k
 simp only [KMX_CopyMeaning.loop_spec]
 split <;> split <;> split <;> simp_all <;> omega
/-- A proved one-window native observation plus the retained frame law can
be composed without inspecting a concrete whole buffer. -/
theorem disjoint_frame {α : Type} (src dst : Nat → α)
 (start count k : Nat) (outside : k < start ∨ start+count ≤ k) :
 KMX_CopyMeaning.loop src dst start count k=dst k :=
 KMX_CopyMeaning.copy_frame src dst start count k outside
/-- Disjoint windows commute. The source is immutable and identical at
both writes; overlapping or aliased native memory is not admitted here. -/
theorem disjoint {α : Type} (src dst : Nat → α) (a n b m : Nat)
 (separate : a+n ≤ b ∨ b+m ≤ a) :
 KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst a n) b m =
 KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst b m) a n := by
 funext k
 simp only [KMX_CopyMeaning.loop_spec]
 split <;> split <;> simp_all <;> omega
#print axioms adjacent
#print axioms disjoint_frame
#print axioms disjoint
end NBW_Window
