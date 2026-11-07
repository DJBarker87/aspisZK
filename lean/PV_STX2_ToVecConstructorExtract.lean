import PV_STX2_ToVecConstructorReturn
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecConstructorExtract
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. The actual f31
Result discriminant is source control, independent of every native handler. -/
theorem match_step (resources : Resources) (encode : Encode)
    (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parents : List Frame) (after : List PV_STX2_SliceSyntax.Node)
    (a : Nat) (w : OWNER) :
    let c : Config := ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.node21 :: after},parents,s⟩
    PV_STX2_Source7IterationBindings.step resources encode C K P H c w =
      step C K (fun _ => none) H c w := by
  dsimp only
  unfold PV_STX2_Source7IterationBindings.step
  rw [PV_STX2_IterationHandlerLocal.bindings2_step C K P _ H _ w (by intro q bad; cases bad)]
  rw [PV_STX2_Source7QUniformAgreement2.neutral C K P H
    ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.node21 :: after},parents,s⟩ w ⟨True.intro,rfl⟩]
  exact PV_STX2_CallSummaryDispatch.step C K P (fun _ => none) H _ w rfl
/-- Conditional on owner acceptance of the translator patch. Extract the
actual returned f35 payload on the installed interpreter, using the named
source2 law and the existing scalar/aggregate compatibility. -/
theorem source2 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parents : List Frame) (after : List PV_STX2_SliceSyntax.Node)
    (a : Nat) (inner : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (input : s.cells ⟨a,4,[]⟩ = some (PV_STX2_Source7QConstructorResult.value inner)) :
    let K := PV_STX2_Source7QAllocationCall.control ctrl
    let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
    PV_STX2_Source7IterationBindings.advance resources encode C K P H 2
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 7 ++ after},parents,s⟩,w,prior⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 9 ++ after},parents,
        PV_STX2_Source7QResultIntoF31.stored s a inner⟩,w,prior⟩ := by
  dsimp only
  let K := PV_STX2_Source7QAllocationCall.control ctrl
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  have old := PV_STX2_Source7QResultIntoF31.source2 C ctrl H s parents after a inner w input
  have moved := PV_STX2_SliceRunExtension.advance_eq (PV_STX2_Source7QRuntimeValues.carrier C)
    C.aggregate (by
      intro tag values value h
      exact PV_STX2_Source7QUniformHeaderCarrier.preserves _ tag values value
        (PV_STX2_Source7QOriginalAllocatedTable.preserves_runtime _ K H tag values value h))
    K (fun _ => none) H 2 _ (by rw [old]; intro site stored bad; cases bad)
  rw [PV_STX2_Source7QUniformReturnCompatibility.runtime_eq] at moved
  have native := moved.trans old
  have framed := congrArg (PV_STX2_SlicePrefixEvents.prepend prior) native
  rw [← PV_STX2_SlicePrefixEvents.advance_prepend] at framed
  simp only [PV_STX2_SlicePrefixEvents.prepend,List.append_nil] at framed
  have first : step C K (fun _ => none) H
      ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 7 ++ after},parents,s⟩ w =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.node22 ::
        (PV_STX2_Source7CtorF31.program.body.drop 9 ++ after)},parents,s⟩,w,[]⟩ := by
    simp [PV_STX2_SliceMachine.step,PV_STX2_Source7CtorF31.program,PV_STX2_Source7CtorF31.block64,
      PV_STX2_Source7CtorF31.node21,PV_STX2_Source7CtorF31.block7,selectVariant,
      PV_STX2_Store.read,locate,input,K,PV_STX2_Source7QAllocationCall.control,
      PV_STX2_Source7QConstructorResult.value,PV_STX2_Source7QConstructorResult.kind,
      PV_STX2_Source7CtorF35.node144,PV_STX2_Aggregates.pack]
  have same := match_step resources encode C K P H s parents
    (PV_STX2_Source7CtorF31.node22 :: (PV_STX2_Source7CtorF31.program.body.drop 9 ++ after)) a w
  change PV_STX2_Source7IterationBindings.step resources encode C K P H
    ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 7 ++ after},parents,s⟩ w = _ at same
  have last := PV_STX2_CallSummaryStraight.run resources encode C K P H
    [PV_STX2_Source7CtorF31.node22] (PV_STX2_Source7CtorF31.program.body.drop 9 ++ after)
    a parents [] s w prior
    (by intro node hn; simp only [List.mem_singleton] at hn; subst node; exact Or.inr ⟨_,rfl,True.intro,True.intro⟩)
    (by intro node hn; simp only [List.mem_singleton] at hn; subst node; rfl)
  have dispatched := PV_STX2_CallSummaryDispatch.run C K P (fun _ => none) H
    [PV_STX2_Source7CtorF31.node22] (PV_STX2_Source7CtorF31.program.body.drop 9 ++ after)
    a parents [] s w prior
    (by intro node hn; simp only [List.mem_singleton] at hn; subst node; exact Or.inr ⟨_,rfl,True.intro,True.intro⟩)
  let c : Config := ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 7 ++ after},parents,s⟩
  let next : Prefix OWNER PV_RJ4IDB.NativeEvent :=
    ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.node22 ::
      (PV_STX2_Source7CtorF31.program.body.drop 9 ++ after)},parents,s⟩,w,prior⟩
  have sameFirst : PV_STX2_Source7IterationBindings.step resources encode C K P H c w =
      step C K (fun _ => none) H c w := same
  have nativeFirst : advance C K (fun _ => none) H 1 ⟨.running c,w,prior⟩ = next := by
    simp only [PV_STX2_SliceMachine.advance,c,first,List.append_nil]
    rfl
  have installedFirst : PV_STX2_Source7IterationBindings.advance resources encode C K P H 1
      ⟨.running c,w,prior⟩ = next := by
    simpa only [PV_STX2_Source7IterationBindings.advance,
      PV_STX2_SliceMachine.advance,sameFirst] using nativeFirst
  change advance C K (fun _ => none) H 2 ⟨.running c,w,prior⟩ = _ at framed
  rw [show 2=1+1 by omega,PV_STX2_SliceDriverBuiltin.advance_add,nativeFirst] at framed
  change PV_STX2_Source7IterationBindings.advance resources encode C K P H (1+1)
    ⟨.running c,w,prior⟩ = _
  rw [PV_STX2_Source7IterationBindings.advance_add,installedFirst]
  change PV_STX2_Source7IterationBindings.advance resources encode C K P H 1 next =
    advance C K P H 1 next at last
  change advance C K P H 1 next = advance C K (fun _ => none) H 1 next at dispatched
  exact last.trans (dispatched.trans framed)

#print axioms match_step
#print axioms source2
end PV_STX2_ToVecConstructorExtract
