import NMD_CutState
set_option autoImplicit false
noncomputable section
namespace NMK_FrameFinding
open NMD_CutState
/-- The predecessor CommonArguments relation contains no postPhysical clause.
Even both complete argument/frame checks permit two different post-heaps.
This is an interface observation, not a counterexample to the deployed code. -/
theorem two_posts {Ambient X Physical : Type} (s : Parent Ambient X Physical)
 (p q : Physical) (different : p ≠ q) :
 CommonArguments (⟨s,s,p⟩ : CommonBoundary Ambient X Physical) ∧
 CommonArguments (⟨s,s,q⟩ : CommonBoundary Ambient X Physical) ∧
 (⟨s,s,p⟩ : CommonBoundary Ambient X Physical).postPhysical ≠
 (⟨s,s,q⟩ : CommonBoundary Ambient X Physical).postPhysical :=
 ⟨rfl,rfl,different⟩
#print two_posts
#print axioms two_posts
end NMK_FrameFinding
