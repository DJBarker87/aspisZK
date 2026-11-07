import PV_STX2_SliceF7
import PV_FN_SLICE_ValueCarrier
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_Suffix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input
/-- INTERNAL boundary after successful drop178, on the actual full post-store.
The return value was produced by f8 and is not reconstructed from a read later. -/
structure Pre {E : Type} (x : Input E) : Prop where
  value : x.s.cells ⟨x.a,0,[]⟩ = some x.ptr
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation

def store1 {E : Type} (x : Input E) := write x.s ⟨x.a,3,[]⟩ none
def store2 {E : Type} (x : Input E) := write (store1 x) ⟨x.a,2,[]⟩ none
def store3 {E : Type} (x : Input E) := write (store2 x) ⟨x.a,1,[]⟩ none
def finalStore {E : Type} (x : Input E) :=
  write (write (store3 x) ⟨x.a,0,[]⟩ (some x.ptr)) ⟨x.parent.activation,x.dest,[]⟩ (some x.ptr)

theorem run {E : Type} (x : Input E) (pre : Pre x) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 5
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 5},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
      ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,finalStore x⟩,x.w,x.es⟩,x.stack⟩ := by
  let B := PV_FN_SLICE_ValueCarrier.carrier x.C
  let q (n : Nat) (t : Store Data) : PV_THR2_IntrinsicState.State OWNER E :=
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop n},
      x.parent :: x.parents,t⟩,x.w,x.es⟩,x.stack⟩
  have h0 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 5 x.s) = q 6 (store1 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node5 :: PV_STX2_SliceF7.program.body.drop 6},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node5
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h1 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 6 (store1 x)) = q 7 (store2 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node6 :: PV_STX2_SliceF7.program.body.drop 7},x.parent :: x.parents,store1 x⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node6
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  have h2 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 7 (store2 x)) = q 8 (store3 x) := by
    change PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.node7 :: PV_STX2_SliceF7.program.body.drop 8},x.parent :: x.parents,store2 x⟩,x.w,x.es⟩,x.stack⟩ = _
    unfold PV_STX2_SliceF7.node7
    exact PV_THR2_IntrinsicFrameSteps.storage B x.K x.P x.H _ _ _ _ _ _ _ _ _ _ _
  let completed : PV_THR2_IntrinsicState.State OWNER E :=
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 8,completed := some (.ok x.ptr)},
      x.parent :: x.parents,store3 x⟩,x.w,x.es⟩,x.stack⟩
  have h3 : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1 (q 8 (store3 x)) = completed := by
    apply PV_THR2_IntrinsicNestedReturn.nested
    simp [store3,store2,store1,write,pre.value]
  have h4 := PV_THR2_InlineFinalStoreContinuation.boundary B x.K x.P x.H
    (store3 x) x.a x.dest (PV_STX2_SliceF7.program.body.drop 8)
    x.parent x.parents x.wait x.ptr x.w x.es x.stack pre.saved pre.action
  rw [PV_THR2_InlineChildReturn.delivered_success B _ x.wait x.a x.dest x.ptr x.w x.es pre.action] at h4
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 5 (q 5 x.s) = _
  rw [show 5=1+4 by omega,PV_THR2_IntrinsicComposition.advance_add,h0,
    show 4=1+3 by omega,PV_THR2_IntrinsicComposition.advance_add,h1,
    show 3=1+2 by omega,PV_THR2_IntrinsicComposition.advance_add,h2,
    show 2=1+1 by omega,PV_THR2_IntrinsicComposition.advance_add,h3]
  exact h4

theorem frame {E : Type} (x : Input E) (p : Address)
    (own : p.activation ≠ x.a) (destination : p ≠ ⟨x.parent.activation,x.dest,[]⟩) :
    (finalStore x).cells p = x.s.cells p := by
  have diff (n : Nat) : p ≠ (⟨x.a,n,[]⟩ : Address) := by
    intro h; exact own (congrArg Address.activation h)
  simp only [finalStore,store3,store2,store1,write,if_neg destination,
    if_neg (diff 0),if_neg (diff 1),if_neg (diff 2),if_neg (diff 3)]
#print axioms run
#print axioms frame
end PV_FN_SLICE_f7_Suffix
