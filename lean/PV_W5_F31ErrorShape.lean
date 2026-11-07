import PV_W5_F31Classify
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31ErrorShape
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

/-- The provider's own value predicate fixes both error representations.
The payload is not inferred merely from an arbitrary enum discriminant. -/
theorem value_error (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K ctrl : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w post : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (value : Data)
    (vp : PV_FN_SLICE_f35.ValuePost resources encode base K s parents a n false
      PV_STX2_Source7GlobalClone.value w external backend value post)
    (error : (PV_FN_SLICE_f31.L ctrl).variant value=some 1) :
    value=PV_W5_F35ErrorValues.result ∨
      value=PV_W5_F35AllocError.result (PV_STX2_Source7QLayoutValues.layout (PV_STX2_Source7CapacityPaths.bytes n)) := by
  unfold PV_FN_SLICE_f35.ValuePost at vp
  dsimp only at vp
  split at vp
  · exact Or.inl vp
  · split at vp
    · rw [vp.1] at error
      change some 0=some 1 at error
      cases error
    · rcases vp with success | failure
      · rcases success with ⟨pointer,_,shape,_⟩
        rw [shape] at error
        change some 0=some 1 at error
        cases error
      · exact Or.inr failure.2

#print axioms value_error
end PV_W5_F31ErrorShape
