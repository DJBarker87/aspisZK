import PV_W5_F31ErrorCase
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Complete
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem error_contract(resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects)
    (value : Data) (returned : (PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend).answer = .returned (.ok value))
    (error : (PV_FN_SLICE_f31.L ctrl).variant value = some 1) :
    PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend := by
  have child := PV_W5_F31Child.instantiated resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have vp := PV_W5_F31Classify.boundary_value resources encode base (PV_FN_SLICE_f31.L ctrl)
    (PV_W5_F31Child.entered s (parent::parents) a n).store (PV_W5_F31Child.parent s (parent::parents) a n)
    (parent::parents) s.nextActivation n false PV_STX2_Source7GlobalClone.value w external backend
    (PV_W5_F31Child.outcome resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w external backend).2
    value child.2.2.1 returned
  have shape := PV_W5_F31ErrorShape.value_error resources encode base (PV_FN_SLICE_f31.L ctrl) ctrl
    (PV_W5_F31Child.entered s (parent::parents) a n).store
    (PV_W5_F31Child.parent s (parent::parents) a n::parent::parents) s.nextActivation n w _ external backend value vp error
  rcases shape with overflow | allocation
  · rw [overflow] at returned
    exact canonical_error_contract resources encode base ctrl s parent parents a n w prior external backend effects
      pre malloc_semantics calloc_semantics global_drop_semantics PV_W5_F35ErrorValues.reserveError returned
  · rw [allocation] at returned
    exact canonical_error_contract resources encode base ctrl s parent parents a n w prior external backend effects
      pre malloc_semantics calloc_semantics global_drop_semantics
      (PV_W5_F35AllocError.reserve (PV_STX2_Source7QLayoutValues.layout (PV_STX2_Source7CapacityPaths.bytes n))) returned

#print error_contract
#print axioms error_contract
end PV_W5_F31Complete
