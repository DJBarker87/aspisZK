import PV_W5_F31SuccessJoin
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Complete
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem success_contract(resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects)
    (pointer : Nat)
    (returned : (PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend).answer = .returned (.ok (PV_STX2_Source7QConstructorResult.value
      (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value)))) :
    PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend := by
  let H := PV_FN_SLICE_f31.handler resources encode base ctrl s (parent::parents) a n external backend
  let D := PV_FN_SLICE_f31.C base ctrl H
  let r := PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend
  change r.answer = _ at returned
  have selected : H (.child PV_STX2_Source7ConstructorEntry.callee s.nextActivation
      [.number n,PV_STX2_Source7ConstructorEntry.initValue,PV_STX2_Source7GlobalClone.value,PV_STX2_Source7LayoutConstructor.value]) w = r := by
    simp only [H,PV_FN_SLICE_f31.handler,ite_true]
    rfl
  have fuel : PV_FN_SLICE_f31.fuel resources encode base ctrl s (parent::parents) a n w external backend=43 := by
    unfold PV_FN_SLICE_f31.fuel
    dsimp only
    change (match r.answer with
      | .returned (.ok value) =>
        if (PV_FN_SLICE_f31.L ctrl).variant value=some 0 then 43
        else match (PV_FN_SLICE_f31.errorReply s value r.world backend).answer with
          | .returned (.ok _) => 22
          | _ => 13
      | _ => 8)=43
    rw [returned]
    rfl
  have delivery : PV_W5_F31Replies.received D s (parent::parents) a (.number n)
      PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value r prior =
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parent::parents,
        PV_W5_F31SuccessJoin.cut s a n pointer⟩,r.world,prior++r.events⟩ := by
    rcases r with ⟨answer,post,events⟩
    cases returned
    rfl
  have child := PV_W5_F31Child.instantiated resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have registry := PV_W5_F31Child.registry resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have run : PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend =
      ⟨.running ⟨{activation:=a,remaining:=[PV_STX2_Source7CtorF31.node63],completed:=some (.ok
        (PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value))},parent::parents,
        PV_STX2_Source7QF31Suffix.stored (PV_W5_F31SuccessJoin.extracted s a n pointer) a n⟩,r.world,prior++r.events⟩ := by
    unfold PV_FN_SLICE_f31.outcome
    rw [fuel]
    change PV_STX2_Source7IterationBindings.advance resources encode D (PV_FN_SLICE_f31.L ctrl)
      (fun _ => none) H 43 (PV_FN_SLICE_f31.start s (parent::parents) a w prior)=_
    rw [show 43=8+35 by omega,PV_STX2_Source7IterationBindings.advance_add]
    have pref := PV_W5_F31Replies.source8 resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base (PV_FN_SLICE_f31.L ctrl) H)
      (PV_FN_SLICE_f31.L ctrl) H s (parent::parents) a _ _ _ w prior pre.length pre.allocator pre.layout
    rw [selected] at pref
    change PV_STX2_Source7IterationBindings.advance resources encode D (PV_FN_SLICE_f31.L ctrl)
      (fun _ => none) H 8 (PV_FN_SLICE_f31.start s (parent::parents) a w prior)=
      PV_W5_F31Replies.received D s (parent::parents) a (.number n)
        PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value r prior at pref
    rw [pref,delivery]
    exact PV_W5_F31SuccessJoin.source35 resources encode base ctrl H s parent parents a n pointer r.world
      (prior++r.events) pre.live pre.usize pre.length pre.layout
  have storeFrame := PV_W5_F35OutcomeFrames.trans s (PV_W5_F31SuccessJoin.cut s a n pointer) _ a
    (PV_W5_F31SuccessStore.returned_frame s a (.number n) _ _ _)
    (PV_W5_F35OutcomeFrames.trans (PV_W5_F31SuccessJoin.cut s a n pointer)
      (PV_W5_F31SuccessJoin.extracted s a n pointer) _ a
      (PV_W5_F31SuccessStore.extracted_frame _ a _)
      (PV_W5_F31SuccessStore.suffix_frame _ a n))
  unfold PV_FN_SLICE_f31.Post
  rw [fuel,run]
  refine ⟨by omega,?_,?_,⟨r.events,rfl⟩,child⟩
  · exact ⟨rfl,rfl,⟨pointer,rfl⟩,returned,rfl⟩
  · exact ⟨storeFrame,registry.1,registry.2,PV_STX2_OwnerActivationWellFormed.mono
      (PV_STX2_OwnerRegistryFrame.invariant pre.wellFormed registry.1 registry.2) storeFrame.1⟩

#print success_contract
#print axioms success_contract
end PV_W5_F31Complete
