import PV_STX2_SliceF8
import PV_FN_SLICE_ValueCarrier
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f8_Suffix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input
/-- INTERNAL f6 success boundary, not the whole-row Pre: its exact result
slot and full post-store/world/events must be supplied by the callee contract. -/
structure Pre {E : Type} (x : Input E) : Prop where
  result : x.s.cells ⟨x.a,4,[]⟩ = some x.ptr
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation

def kind : Data := match PV_STX2_SliceF8.node11 with
  | .leaf (.aggregateMove _ _ k _) => k | _ => .null
def value (v : Data) := PV_STX2_Aggregates.pack kind [v]
def store1 {E : Type} (x : Input E) := write x.s ⟨x.a,6,[]⟩ none
def store2 {E : Type} (x : Input E) := write (store1 x) ⟨x.a,5,[]⟩ none
def store3 {E : Type} (x : Input E) := write (write (store2 x) ⟨x.a,4,[]⟩ none) ⟨x.a,0,[]⟩ (some (value x.ptr))
def store4 {E : Type} (x : Input E) := write (store3 x) ⟨x.a,4,[]⟩ none
def store5 {E : Type} (x : Input E) := write (store4 x) ⟨x.a,3,[]⟩ none
def store6 {E : Type} (x : Input E) := write (store5 x) ⟨x.a,2,[]⟩ none
def store7 {E : Type} (x : Input E) := write (store6 x) ⟨x.a,1,[]⟩ none
def finalStore {E : Type} (x : Input E) :=
  write (write (store7 x) ⟨x.a,0,[]⟩ (some (value x.ptr))) ⟨x.parent.activation,x.dest,[]⟩ (some (value x.ptr))

/-- No callee internals, discarded source cells or silent store replacement.
Native failure/pending cases belong to the pending all-answer assembly. -/
theorem run {E : Type} (x : Input E) (pre : Pre x) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 9
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop 9},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
      ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,finalStore x⟩,x.w,x.es⟩,x.stack⟩ := by
  let B := PV_FN_SLICE_ValueCarrier.carrier x.C
  let q (n : Nat) (t : Store Data) : PV_THR2_IntrinsicState.State OWNER E :=
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop n},x.parent :: x.parents,t⟩,x.w,x.es⟩,x.stack⟩
  have h0 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 9 x.s) = q 10 (store1 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node9 :: PV_STX2_SliceF8.program.body.drop 10},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node9
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h1 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 10 (store1 x)) = q 11 (store2 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node10 :: PV_STX2_SliceF8.program.body.drop 11},x.parent :: x.parents,(store1 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node10
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h2 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 11 (store2 x)) = q 12 (store3 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node11 :: PV_STX2_SliceF8.program.body.drop 12},x.parent :: x.parents,(store2 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node11
    rw [PV_THR2_IntrinsicFrameAggregate.run]
    have agg : B.aggregate kind [x.ptr] = some (value x.ptr) := rfl
    change PV_THR2_IntrinsicFrameAggregate.after B (store2 x) x.a (x.parent :: x.parents) []
      (PV_STX2_SliceF8.program.body.drop 12) _ (.local 0) kind [.move (.local 4)] x.w x.es x.stack = _
    simp [PV_THR2_IntrinsicFrameAggregate.after,PV_STX2_Store.bind,evaluate,operands,operand,
      PV_STX2_Store.read,readAddress,readFields,locate,writeAddress,write,store1,store2,store3,
      pre.result,agg,q]
  have h3 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 12 (store3 x)) = q 13 (store4 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node12 :: PV_STX2_SliceF8.program.body.drop 13},x.parent :: x.parents,(store3 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node12
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h4 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 13 (store4 x)) = q 14 (store5 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node13 :: PV_STX2_SliceF8.program.body.drop 14},x.parent :: x.parents,(store4 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node13
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h5 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 14 (store5 x)) = q 15 (store6 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node14 :: PV_STX2_SliceF8.program.body.drop 15},x.parent :: x.parents,(store5 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node14
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h6 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 15 (store6 x)) = q 16 (store7 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.node15 :: PV_STX2_SliceF8.program.body.drop 16},x.parent :: x.parents,(store6 x)⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF8.node15
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  let completed : PV_THR2_IntrinsicState.State OWNER E :=
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop 16,completed := some (.ok (value x.ptr))},x.parent :: x.parents,store7 x⟩,x.w,x.es⟩,x.stack⟩
  have h7 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 16 (store7 x)) = completed := by
    apply PV_THR2_IntrinsicNestedReturn.nested
    simp [store7,store6,store5,store4,store3,write]
  have h8 := PV_THR2_InlineFinalStoreContinuation.boundary B x.K x.P x.H
    (store7 x) x.a x.dest (PV_STX2_SliceF8.program.body.drop 16)
    x.parent x.parents x.wait (value x.ptr) x.w x.es x.stack pre.saved pre.action
  rw [PV_THR2_InlineChildReturn.delivered_success B _ x.wait x.a x.dest
    (value x.ptr) x.w x.es pre.action] at h8
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 9 (q 9 x.s) = _
  rw [show 9=1+8 by omega,PV_THR2_IntrinsicComposition.advance_add,h0,
    show 8=1+7 by omega,PV_THR2_IntrinsicComposition.advance_add,h1,
    show 7=1+6 by omega,PV_THR2_IntrinsicComposition.advance_add,h2,
    show 6=1+5 by omega,PV_THR2_IntrinsicComposition.advance_add,h3,
    show 5=1+4 by omega,PV_THR2_IntrinsicComposition.advance_add,h4,
    show 4=1+3 by omega,PV_THR2_IntrinsicComposition.advance_add,h5,
    show 3=1+2 by omega,PV_THR2_IntrinsicComposition.advance_add,h6,
    show 2=1+1 by omega,PV_THR2_IntrinsicComposition.advance_add,h7]
  exact h8

/-- The emitted NeverShortCircuit wrapper has exactly the returned inner value. -/
theorem value_field (C : Carrier OWNER Data) (v : Data) :
    (PV_FN_SLICE_ValueCarrier.carrier C).field (value v) 0 = some v := rfl

theorem frame {E : Type} (x : Input E) (p : Address)
    (own : p.activation ≠ x.a) (destination : p ≠ ⟨x.parent.activation,x.dest,[]⟩) :
    (finalStore x).cells p = x.s.cells p := by
  have diff (n : Nat) : p ≠ (⟨x.a,n,[]⟩ : Address) := by
    intro h; exact own (congrArg Address.activation h)
  simp only [finalStore,store7,store6,store5,store4,store3,store2,store1,write,
    if_neg destination,if_neg (diff 0),if_neg (diff 1),if_neg (diff 2),if_neg (diff 3),
    if_neg (diff 4),if_neg (diff 5),if_neg (diff 6)]
#print axioms run
#print axioms frame
#print axioms value_field
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print run
end PV_FN_SLICE_f8_Suffix
