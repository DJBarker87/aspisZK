import PV_W5_F31Exceptional
import PV_W5_F31Success
import PV_W5_F31Error
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem PV_FN_SLICE_f31.contract
    (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects) :
    PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend := by
  have childClosed := PV_FN_SLICE_f35.contract resources encode base (PV_FN_SLICE_f31.L ctrl)
    (PV_W5_F31Child.entered s (parent::parents) a n).store
    (PV_W5_F31Child.parent s (parent::parents) a n) (parent::parents) s.nextActivation n false
    PV_STX2_Source7GlobalClone.value w [] external backend effects
    (PV_W5_F35CallContext.f31_entry s (parent::parents) a n w pre.wellFormed pre.usize pre.registered)
    malloc_semantics calloc_semantics global_drop_semantics
  have allCases : PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend := by
    let r := PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend
    have terminal := PV_W5_F31Complete.exceptional_contract resources encode base ctrl s parent parents a n w prior external backend effects pre malloc_semantics calloc_semantics global_drop_semantics
    cases answer : r.answer with
    | pending => exact terminal (by intro value bad; change r.answer=.returned (.ok value) at bad; rw [answer] at bad; cases bad)
    | fault f => exact terminal (by intro value bad; change r.answer=.returned (.ok value) at bad; rw [answer] at bad; cases bad)
    | returned result =>
      cases result with
      | fail error => exact terminal (by intro value bad; change r.answer=.returned (.ok value) at bad; rw [answer] at bad; cases bad)
      | div => exact terminal (by intro value bad; change r.answer=.returned (.ok value) at bad; rw [answer] at bad; cases bad)
      | ok value =>
        rcases PV_W5_F31Child.classify resources encode base ctrl s parent parents a n w prior external backend effects pre malloc_semantics calloc_semantics global_drop_semantics value answer with success | error
        · rcases success with ⟨pointer,shape⟩
          subst value
          exact PV_W5_F31Complete.success_contract resources encode base ctrl s parent parents a n w prior external backend effects pre malloc_semantics calloc_semantics global_drop_semantics pointer answer
        · exact PV_W5_F31Complete.error_contract resources encode base ctrl s parent parents a n w prior external backend effects pre malloc_semantics calloc_semantics global_drop_semantics value answer error
  exact ⟨allCases.1,allCases.2.1,allCases.2.2.1,allCases.2.2.2.1,childClosed⟩

#print PV_FN_SLICE_f31.contract
#print axioms PV_FN_SLICE_f31.contract
