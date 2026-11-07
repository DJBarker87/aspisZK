import PV_FN_SLICE_f8_PrefixData
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f8_Prefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_SLICE_f8_PrefixData
def regular (kind generics : Data) : Data := .object [("Regular",.object [("kind",kind),("generics",generics)])]
/-- Static call issue with the exact emitted cleanup retained. Only argument
binding occurs; no child body, reply, failure or pending branch is discarded. -/
theorem issue {E : Type} (B : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s t : Store Data) (a : Nat) (parents : List Frame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : Site) (kind generics : Data)
    (args : List Operand) (vs : List Data) (dest : Nat) (cleanup : List Instruction)
    (w : OWNER) (es : List E) (stack : List Config)
    (evaluated : operands B w a args s = some (vs,t)) :
    PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.call site (regular kind generics) args (.local dest) cleanup) :: rest},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := rest,waiting := some ⟨.child (regular kind generics) t.nextActivation vs,.child t.nextActivation (.local dest),cleanup⟩},parents,PV_THR2_StaticCall.issued t vs⟩,w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,evaluated,PV_THR2_StaticCall.issued,regular]

def kindGenerics : Data × Data := match PV_STX2_SliceF8.node8 with
  | .leaf (.call _ (.object [("Regular",.object [("kind",k),("generics",g)])]) _ _ _) => (k,g)
  | _ => (.null,.null)

def metadata : Data := match PV_STX2_SliceF8.node5 with
  | .leaf (.bind _ _ (.reference _ (.constant c))) => c | _ => .null

theorem run {E : Type} (x : Input E) (pre : Pre x) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 9
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = out x := by
  let B := PV_FN_SLICE_ValueCarrier.carrier x.C
  let q (n : Nat) (t : Store Data) : PV_THR2_IntrinsicState.State OWNER E :=
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop n},x.parent :: x.parents,t⟩,x.w,x.es⟩,x.stack⟩
  have h0 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 0 x.s) = q 1 (store1 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node0 :: PV_STX2_SliceF8.program.body.drop 1},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node0
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h1 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 1 (store1 x)) = q 2 (store2 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node1 :: PV_STX2_SliceF8.program.body.drop 2},x.parent :: x.parents,(store1 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node1
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h2 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 2 (store2 x)) = q 3 (store3 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node2 :: PV_STX2_SliceF8.program.body.drop 3},x.parent :: x.parents,(store2 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node2
    rw [PV_THR2_IntrinsicFrameBind.run]
    simp [PV_THR2_IntrinsicFrameBind.after,PV_STX2_Store.bind,evaluate,operand,
      PV_STX2_Store.read,locate,writeAddress,replaceFields,readFields,write,
      store1,store2,store3,emptied,pre.tuple,PV_FN_SLICE_ValueCarrier.carrier,
      PV_STX2_Aggregates.carrier,PV_STX2_Aggregates.pack,PV_STX2_Aggregates.slotValue,
      PV_STX2_Aggregates.updateSlots,q,B]
  have h3 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 3 (store3 x)) = q 4 (store4 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node3 :: PV_STX2_SliceF8.program.body.drop 4},x.parent :: x.parents,(store3 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node3
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h4 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 4 (store4 x)) = q 5 (store5 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node4 :: PV_STX2_SliceF8.program.body.drop 5},x.parent :: x.parents,(store4 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node4
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h5 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 5 (store5 x)) = q 6 (store6 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node5 :: PV_STX2_SliceF8.program.body.drop 6},x.parent :: x.parents,(store5 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node5
    rw [PV_THR2_IntrinsicFrameBind.run]
    have unit : B.constant metadata = some .null := rfl
    have pointer : B.dereference x.w (PV_STX2_TypedReferences.reference x.capture .null) = some x.capture :=
      PV_STX2_TypedReferences.dereference x.C x.w x.capture .null
    have reference (p : Address) : B.reference p .null = PV_STX2_TypedReferences.reference p .null := rfl
    change PV_THR2_IntrinsicFrameBind.after B (store5 x) x.a (x.parent :: x.parents) []
      (PV_STX2_SliceF8.program.body.drop 6) _ (.local 5)
      (.reference (.project (.project (.local 1) .deref) (.field 0)) (.constant metadata)) x.w x.es x.stack = _
    simp [PV_THR2_IntrinsicFrameBind.after,PV_STX2_Store.bind,evaluate,operand,
      PV_STX2_Store.read,locate,writeAddress,write,unit,pointer,reference,
      store1,store2,store3,store4,store5,store6,pre.self,generator,q]
  have h6 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 6 (store6 x)) = q 7 (store7 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node6 :: PV_STX2_SliceF8.program.body.drop 7},x.parent :: x.parents,(store6 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node6
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h7 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 7 (store7 x)) = q 8 (store8 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node7 :: PV_STX2_SliceF8.program.body.drop 8},x.parent :: x.parents,(store7 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node7
    rw [PV_THR2_IntrinsicFrameAggregate.run]
    have agg : B.aggregate tupleKind [.number x.index] = some (tuple x.index) := rfl
    change PV_THR2_IntrinsicFrameAggregate.after B (store7 x) x.a (x.parent :: x.parents) []
      (PV_STX2_SliceF8.program.body.drop 8) _ (.local 6) tupleKind [.copy (.local 3)] x.w x.es x.stack = _
    simp [PV_THR2_IntrinsicFrameAggregate.after,PV_STX2_Store.bind,evaluate,operands,operand,
      PV_STX2_Store.read,locate,writeAddress,write,agg,
      store3,store4,store5,store6,store7,store8,q]
  have h8 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 8 (store8 x)) = out x := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node8 :: PV_STX2_SliceF8.program.body.drop 9},x.parent :: x.parents,store8 x⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node8
    have evaluated : operands B x.w x.a source.2.2.1 (store8 x) =
        some ([generator x,tuple x.index],moved x) := by
      change operands B x.w x.a [.move (.local 5),.move (.local 6)] (store8 x) = _
      simp [operands,operand,PV_STX2_Store.read,locate,writeAddress,write,store8,store7,store6,moved]
    exact issue B x.K x.P x.H (store8 x) (moved x) x.a (x.parent :: x.parents)
      (PV_STX2_SliceF8.program.body.drop 9) source.1 kindGenerics.1 kindGenerics.2
      source.2.2.1 [generator x,tuple x.index] 4 source.2.2.2.2 x.w x.es x.stack evaluated
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 9 (q 0 x.s) = _
  rw [show 9=1+8 by omega,PV_THR2_IntrinsicComposition.advance_add,h0,
    show 8=1+7 by omega,PV_THR2_IntrinsicComposition.advance_add,h1,
    show 7=1+6 by omega,PV_THR2_IntrinsicComposition.advance_add,h2,
    show 6=1+5 by omega,PV_THR2_IntrinsicComposition.advance_add,h3,
    show 5=1+4 by omega,PV_THR2_IntrinsicComposition.advance_add,h4,
    show 4=1+3 by omega,PV_THR2_IntrinsicComposition.advance_add,h5,
    show 3=1+2 by omega,PV_THR2_IntrinsicComposition.advance_add,h6,
    show 2=1+1 by omega,PV_THR2_IntrinsicComposition.advance_add,h7]
  exact h8
#print axioms issue
#print axioms run
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print run
end PV_FN_SLICE_f8_Prefix
