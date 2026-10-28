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
 by_cases hp : start+left≤k ∧ k<start+left+right <;>
   by_cases hl : start≤k ∧ k<start+left <;>
   by_cases hu : start≤k ∧ k<start+(left+right) <;>
   simp only [hp,hl,hu,if_pos,if_neg] <;> omega
/-- A proved one-window native observation plus the retained frame law can
be composed without inspecting a concrete whole buffer. -/
theorem disjoint_frame {α : Type} (src dst : Nat → α)
 (start count k : Nat) (outside : k < start ∨ start+count ≤ k) :
 KMX_CopyMeaning.loop src dst start count k=dst k :=
 KMX_CopyMeaning.copy_frame src dst start count k outside
/-- Writes from the same immutable source commute, even if their value
windows overlap. Native alias/provenance obligations are separate. -/
theorem disjoint {α : Type} (src dst : Nat → α) (a n b m : Nat)
 :
 KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst a n) b m =
 KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst b m) a n := by
 funext k
 simp only [KMX_CopyMeaning.loop_spec]
 split <;> split <;> simp_all <;> omega
#print axioms adjacent
#print axioms disjoint_frame
#print axioms disjoint
end NBW_Window
