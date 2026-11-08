import PV_THR2_OwnInitBridgedAdequacy
import PV_THR2_OwnInitAllocationBridgedSteps
import PV_THR2_OwnInitAllocationBridgedRetry
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitBridgeTypedRepresentation
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Recount14, thread21: ONLY the typed_representation / binary-structural
category. This names the existing full-state obligation; it neither proves it
nor promotes it to an endpoint premise or a new trust item. No Shape, decoder
success or returned-answer restriction is hidden in the field. -/
structure Facts (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (sourceStep : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent →
      PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) : Prop where
  bridge14756 : PV_THR2_OwnInitBridgedAdequacy.InterpretationAdequacy14756
    C K P resources encode H sourceStep

/-- Conditional source transport of the actual operand step AND full reply
step. The sole representation hypothesis is the named full-state adequacy
obligation in its documented category. It is used at the call and retry, with
all answers and complete source stores/worlds/events/suspended frames intact. -/
theorem two_steps (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (sourceStep : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent →
      PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
    (typedRepresentation : Facts C K P resources encode H sourceStep)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (cell : s.cells ⟨a,46,[]⟩ = some payload) :
    let q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent :=
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 129,loops := loops},parents,s⟩,
        w,es⟩,stack⟩
    sourceStep (sourceStep q) =
      PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H 2 q := by
  intro q
  let t := write s ⟨a,46,[]⟩ none
  let retry := PV_THR2_IntrinsicFrameEnter.pending t a parents loops
    (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361InitChildren.fnAllocationFull [payload] 45
  let middle : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent :=
    ⟨⟨.running retry,w,es⟩,stack⟩
  have first := typedRepresentation.bridge14756 q _ rfl
    (PV_THR2_OwnInitAction.call s a parents loops)
  have moved : operands C w a [.move (.local 46)] s = some ([payload],t) := by
    simp only [operands,operand,PV_STX2_Store.read,locate,cell,writeAddress,
      Bind.bind,Option.bind_some,Pure.pure]
    rfl
  have modelFirst : PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H q = middle := by
    have run := PV_THR2_OwnInitAllocationBridgedSteps.call C K P resources encode H
      s a parents loops w es stack
    change PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H q = _ at run
    rw [run]
    simp only [PV_THR2_IntrinsicFrameCall.after,
      show PV_THR2_Source361AllocationFull.source.2.2.2.1 = [.move (.local 46)] from rfl,moved]
    rfl
  have second := typedRepresentation.bridge14756 middle retry rfl
    (PV_THR2_OwnInitAction.retry t a parents loops payload)
  rw [first,modelFirst,second]
  change _ = PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H
    (PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H q)
  rw [modelFirst]
#print axioms two_steps
end PV_THR2_OwnInitBridgeTypedRepresentation
