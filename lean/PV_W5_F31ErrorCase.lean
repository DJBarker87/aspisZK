import PV_W5_F31Abort
import PV_W5_F31SuccessStore
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Complete
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem canonical_error_contract(resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects)
    (payload : Data)
    (returned : (PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend).answer =
      .returned (.ok (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [payload]))) :
    PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend := by
  let H := PV_FN_SLICE_f31.handler resources encode base ctrl s (parent::parents) a n external backend
  let D := PV_FN_SLICE_f31.C base ctrl H
  let r35 := PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend
  let value := PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [payload]
  let t := PV_W5_F31SuccessStore.returned s a (.number n) PV_STX2_Source7GlobalClone.value
    PV_STX2_Source7LayoutConstructor.value value
  let r36 := PV_STX2_Source7QUniformResourceHandler.lift backend
    (.child PV_W5_NativeLeaves.callee_f36 t.nextActivation [payload]) r35.world
  let z := PV_W5_F31ErrorReply.received D t (parent::parents) a payload r36 (prior++r35.events)
  change r35.answer=.returned (.ok value) at returned
  have selected35 : H (.child PV_STX2_Source7ConstructorEntry.callee s.nextActivation
      [.number n,PV_STX2_Source7ConstructorEntry.initValue,PV_STX2_Source7GlobalClone.value,PV_STX2_Source7LayoutConstructor.value]) w=r35 := by
    simp only [H,PV_FN_SLICE_f31.handler,ite_true]
    rfl
  have selected36 : H (.child PV_W5_NativeLeaves.callee_f36 t.nextActivation [payload]) r35.world=r36 :=
    PV_W5_F31ErrorReply.handler_f36 resources encode base ctrl s (parent::parents) a n t.nextActivation external backend payload r35.world
  have delivery35 : PV_W5_F31Replies.received D s (parent::parents) a (.number n)
      PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value r35 prior =
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parent::parents,t⟩,
        r35.world,prior++r35.events⟩ := by
    rcases r35 with ⟨answer,post,events⟩
    cases returned
    rfl
  have run13 : PV_STX2_Source7IterationBindings.advance resources encode D (PV_FN_SLICE_f31.L ctrl)
      (fun _ => none) H 13 (PV_FN_SLICE_f31.start s (parent::parents) a w prior)=z := by
    have pref := PV_W5_F31Replies.source8 resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base (PV_FN_SLICE_f31.L ctrl) H)
      (PV_FN_SLICE_f31.L ctrl) H s (parent::parents) a _ _ _ w prior pre.length pre.allocator pre.layout
    rw [selected35] at pref
    change PV_STX2_Source7IterationBindings.advance resources encode D (PV_FN_SLICE_f31.L ctrl)
      (fun _ => none) H 8 (PV_FN_SLICE_f31.start s (parent::parents) a w prior)=
      PV_W5_F31Replies.received D s (parent::parents) a (.number n)
        PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value r35 prior at pref
    rw [show 13=8+5 by omega,PV_STX2_Source7IterationBindings.advance_add,pref,delivery35]
    have tail := PV_W5_F31ErrorReply.source5 resources encode D (PV_FN_SLICE_f31.L ctrl) H t (parent::parents) a payload r35.world
      (prior++r35.events) (by simp [t,value,PV_W5_F31SuccessStore.returned,write]) (by rfl) (by rfl) (by rfl)
    rw [selected36] at tail
    exact tail
  have fuelCases : PV_FN_SLICE_f31.fuel resources encode base ctrl s (parent::parents) a n w external backend =
      match r36.answer with | .returned (.ok _) => 22 | _ => 13 := by
    unfold PV_FN_SLICE_f31.fuel
    dsimp only
    change (match r35.answer with
      | .returned (.ok val) =>
        if (PV_FN_SLICE_f31.L ctrl).variant val=some 0 then 43
        else match (PV_FN_SLICE_f31.errorReply s val r35.world backend).answer with
          | .returned (.ok _) => 22
          | _ => 13
      | _ => 8)=_
    rw [returned]
    rfl
  have child := PV_W5_F31Child.instantiated resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have reg35 := PV_W5_F31Child.registry resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have reg36 := PV_W5_NativeFrame.lift_frame backend
    (.child PV_W5_NativeLeaves.callee_f36 t.nextActivation [payload]) r35.world
  have registry : r36.world.places=w.places ∧ r36.world.next=w.next :=
    ⟨reg36.1.trans reg35.1,reg36.2.trans reg35.2⟩
  have initialFrame := PV_W5_F31SuccessStore.returned_frame s a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value value
  have sourceFrame := PV_W5_F31ErrorReply.source_frame D t (parent::parents) a payload r36 (prior++r35.events)
  have frame13 : PV_W5_F59Frame.StoreFrame s (PV_W5_LeafBoundary.statusStore z.status) a :=
    PV_W5_F35OutcomeFrames.trans s t _ a initialFrame sourceFrame
  have wfcut := PV_STX2_OwnerActivationWellFormed.mono
    (PV_STX2_OwnerRegistryFrame.invariant pre.wellFormed reg35.1 reg35.2) initialFrame.1
  have leaf := PV_W5_F31ErrorReply.instantiated D t (parent::parents) a payload r35.world
    (prior++r35.events) backend wfcut
  have wf13 : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed r36.world
      (PV_W5_LeafBoundary.statusStore z.status).nextActivation := by
    have wf := leaf.2.2.2.1
    rw [leaf.2.1] at wf
    rw [PV_W5_F31ErrorReply.leaf_store D t (parent::parents) a payload r36 (prior++r35.events)]
    exact wf
  have worldEvents := PV_W5_F31ErrorReply.world_events D t (parent::parents) a payload r36 (prior++r35.events)
  change z.world=r36.world ∧ z.events=(prior++r35.events)++r36.events at worldEvents
  by_cases success : ∃ v, r36.answer=.returned (.ok v)
  · obtain ⟨v,answer⟩ := success
    let u := PV_W5_LeafBoundary.returnedStore (PV_W5_F31ErrorReply.entry t (parent::parents) a payload) v
    have delivered : z=⟨.running ⟨{activation:=a,remaining:=PV_W5_F31ErrorCall.after},parent::parents,u⟩,
        r36.world,(prior++r35.events)++r36.events⟩ := by
      rcases r36 with ⟨result,post,events⟩
      cases answer
      rfl
    have fuel : PV_FN_SLICE_f31.fuel resources encode base ctrl s (parent::parents) a n w external backend=22 := by
      rw [fuelCases,answer]
    have run : PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend=
        ⟨.fault .abort (PV_W5_F31Abort.stored u a),r36.world,(prior++r35.events)++r36.events⟩ := by
      unfold PV_FN_SLICE_f31.outcome
      rw [fuel]
      change PV_STX2_Source7IterationBindings.advance resources encode D (PV_FN_SLICE_f31.L ctrl)
        (fun _ => none) H 22 (PV_FN_SLICE_f31.start s (parent::parents) a w prior)=_
      rw [show 22=13+9 by omega,PV_STX2_Source7IterationBindings.advance_add,run13,delivered]
      exact PV_W5_F31Abort.source9 resources encode D (PV_FN_SLICE_f31.L ctrl) H u (parent::parents) a r36.world _
    rw [delivered] at frame13 wf13
    have finalFrame := PV_W5_F35OutcomeFrames.trans s u _ a frame13 (PV_W5_F31Abort.frame u a)
    unfold PV_FN_SLICE_f31.Post
    rw [fuel,run]
    exact ⟨by omega,True.intro,⟨finalFrame,registry.1,registry.2,wf13⟩,
      ⟨r35.events++r36.events,List.append_assoc _ _ _⟩,child⟩
  · have exceptional : ∀ v, r36.answer≠.returned (.ok v) := by intro v bad; exact success ⟨v,bad⟩
    have fuel : PV_FN_SLICE_f31.fuel resources encode base ctrl s (parent::parents) a n w external backend=13 := by
      rw [fuelCases]
      cases answer : r36.answer with
      | pending => rfl
      | fault f => rfl
      | returned result =>
        cases result with
        | fail e => rfl
        | div => rfl
        | ok v => exact False.elim (exceptional v answer)
    have run : PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend=z := by
      unfold PV_FN_SLICE_f31.outcome
      rw [fuel]
      exact run13
    have boundary := PV_W5_F31ErrorReply.exceptional_boundary resources encode base ctrl s t parent parents a n w external backend
      D payload r36 (prior++r35.events) (by rfl) exceptional
    unfold PV_FN_SLICE_f31.Post
    rw [fuel,run]
    refine ⟨by omega,boundary,?_,⟨r35.events++r36.events,?_⟩,child⟩
    · unfold PV_W5_F59Frame.Post
      rw [worldEvents.1]
      exact ⟨frame13,registry.1,registry.2,wf13⟩
    · exact worldEvents.2.trans (List.append_assoc _ _ _)

#print axioms canonical_error_contract
end PV_W5_F31Complete
