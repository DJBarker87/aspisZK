import PV_W5_F31ExceptionalReply
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Complete
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

theorem exceptional_contract(resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External)
    (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (pre : PV_FN_SLICE_f31.Pre s (parent::parents) a n w)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects)
    (exceptional : ∀ value, (PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend).answer ≠ .returned (.ok value)) :
    PV_FN_SLICE_f31.Post resources encode base ctrl s parent parents a n w prior external backend := by
  let H := PV_FN_SLICE_f31.handler resources encode base ctrl s (parent::parents) a n external backend
  let D := PV_FN_SLICE_f31.C base ctrl H
  let r := PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend
  have selected : H (.child PV_STX2_Source7ConstructorEntry.callee s.nextActivation
      [.number n,PV_STX2_Source7ConstructorEntry.initValue,PV_STX2_Source7GlobalClone.value,PV_STX2_Source7LayoutConstructor.value]) w = r := by
    simp only [H,PV_FN_SLICE_f31.handler,ite_true]
    rfl
  change ∀ value, r.answer ≠ .returned (.ok value) at exceptional
  have fuel : PV_FN_SLICE_f31.fuel resources encode base ctrl s (parent::parents) a n w external backend=8 := by
    unfold PV_FN_SLICE_f31.fuel
    cases answer : (PV_FN_SLICE_f31.childReply resources encode base ctrl s (parent::parents) a n w external backend).answer with
    | pending => simp only [answer]
    | fault f => simp only [answer]
    | returned result =>
      cases result with
      | fail e => simp only [answer]
      | div => simp only [answer]
      | ok v => exact False.elim (exceptional v answer)
  have run : PV_FN_SLICE_f31.outcome resources encode base ctrl s (parent::parents) a n w prior external backend =
      PV_W5_F31Replies.received D s (parent::parents) a (.number n) PV_STX2_Source7GlobalClone.value
        PV_STX2_Source7LayoutConstructor.value r prior := by
    unfold PV_FN_SLICE_f31.outcome
    rw [fuel]
    change PV_STX2_Source7IterationBindings.advance resources encode D (PV_FN_SLICE_f31.L ctrl) (fun _ => none) H 8 _ = _
    have pref := PV_W5_F31Replies.source8 resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base (PV_FN_SLICE_f31.L ctrl) H)
      (PV_FN_SLICE_f31.L ctrl) H s (parent::parents) a _ _ _ w prior pre.length pre.allocator pre.layout
    rw [selected] at pref
    exact pref
  have child := PV_W5_F31Child.instantiated resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have registry := PV_W5_F31Child.registry resources encode base (PV_FN_SLICE_f31.L ctrl) s (parent::parents) a n w
    external backend effects pre.wellFormed pre.usize pre.registered malloc_semantics calloc_semantics global_drop_semantics
  have worldEvents := PV_W5_F31ExceptionalReply.world_events D s (parent::parents) a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value r prior
  have stored := PV_W5_F31ExceptionalReply.store D s parent parents a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value r prior exceptional
  have frame := PV_W5_F31ExceptionalReply.entered_frame s a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value
  unfold PV_FN_SLICE_f31.Post
  rw [fuel,run]
  refine ⟨by omega,?_,?_,⟨r.events,worldEvents.2⟩,child⟩
  · unfold PV_FN_SLICE_f31.Boundary
    rcases r with ⟨answer,post,events⟩
    cases answer with
    | pending => exact ⟨rfl,rfl,_,rfl,Or.inl rfl⟩
    | fault f => cases f <;> trivial
    | returned result =>
      cases result with
      | fail e => exact ⟨rfl,rfl,True.intro⟩
      | div => exact ⟨rfl,rfl,True.intro⟩
      | ok v => exact False.elim (exceptional v rfl)
  · unfold PV_W5_F59Frame.Post
    rw [stored,worldEvents.1]
    exact ⟨frame,registry.1,registry.2,PV_STX2_OwnerActivationWellFormed.mono
      (PV_STX2_OwnerRegistryFrame.invariant pre.wellFormed registry.1 registry.2) frame.1⟩

#print exceptional_contract
#print axioms exceptional_contract
end PV_W5_F31Complete
