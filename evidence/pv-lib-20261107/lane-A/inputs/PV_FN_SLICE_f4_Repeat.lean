import PV_FN_SLICE_f4_Prefix
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f4_Repeat
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input

def moved {E : Type} (x : Input E) :=
  write (write x.s ⟨x.a,11,[]⟩ none) ⟨x.a,10,[]⟩ (some PV_FN_SLICE_f23.value)
def operations := [PV_STX2_SliceF4.node4,PV_STX2_SliceF4.node5,PV_STX2_SliceF4.node6].map
  PV_FN_SLICE_f9_Prefix.operation
def prepared {E : Type} (x : Input E) := PV_FN_W2_LifetimePrefix.store (moved x) x.a operations
def ready {E : Type} (x : Input E) : Input E := {x with s := prepared x}

/-- INTERNAL four-step continuation. Its only value premise is discharged
below from CLOSED f23's returned slot. It is not a new f4 entry condition. -/
theorem run {E : Type} (x : Input E)
    (value : x.s.cells ⟨x.a,11,[]⟩ = some PV_FN_SLICE_f23.value) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 4
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 3},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 7},
        x.parent :: x.parents,prepared x⟩,x.w,x.es⟩,x.stack⟩ := by
  let B := PV_FN_SLICE_ValueCarrier.carrier x.C
  have first : PV_THR2_IntrinsicState.advance B x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.node3 ::
        PV_STX2_SliceF4.program.body.drop 4},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 4},
        x.parent :: x.parents,moved x⟩,x.w,x.es⟩,x.stack⟩ := by
    unfold PV_STX2_SliceF4.node3
    rw [PV_THR2_IntrinsicFrameBind.run]
    simp [PV_THR2_IntrinsicFrameBind.after,PV_STX2_Store.bind,evaluate,operand,
      PV_STX2_Store.read,locate,readAddress,readFields,writeAddress,value,moved]
  change PV_THR2_IntrinsicState.advance B x.K x.P x.H 4
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.node3 ::
      PV_STX2_SliceF4.program.body.drop 4},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = _
  rw [show 4=1+3 by rfl,PV_THR2_IntrinsicComposition.advance_add,first]
  exact PV_FN_W2_LifetimePrefix.run B x.K x.P x.H operations (moved x) x.a
    (x.parent :: x.parents) [] (PV_STX2_SliceF4.program.body.drop 7) x.w x.es x.stack

def source : Site × Data × List Instruction := match PV_STX2_SliceF4.node7 with
  | .leaf (.call site fn _ _ cleanup) => (site,fn,cleanup)
  | _ => (⟨0,0,.null⟩,.null,[])
def kindGenerics : Data × Data := match PV_STX2_SliceF4.node7 with
  | .leaf (.call _ (.object [("Regular",.object [("kind",k),("generics",g)])]) _ _ _) => (k,g)
  | _ => (.null,.null)
def consumed {E : Type} (x : Input E) := write (prepared x) ⟨x.a,10,[]⟩ none
def issued {E : Type} (x : Input E) := PV_THR2_StaticCall.issued (consumed x) [PV_FN_SLICE_f23.value]
def waiting {E : Type} (x : Input E) : PV_STX2_Native.Waiting Data :=
  ⟨.child source.2.1 x.s.nextActivation [PV_FN_SLICE_f23.value],
    .child x.s.nextActivation (.local 2),source.2.2⟩
def out {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 8,waiting := some (waiting x)},x.parent :: x.parents,issued x⟩,x.w,x.es⟩,x.stack⟩

theorem operand {E : Type} (x : Input E) :
    operands (PV_FN_SLICE_ValueCarrier.carrier x.C) x.w x.a [.move (.local 10)] (prepared x) =
      some ([PV_FN_SLICE_f23.value],consumed x) := by
  simp [operands,PV_STX2_Store.operand,PV_STX2_Store.read,locate,readAddress,
    readFields,writeAddress,prepared,operations,PV_FN_SLICE_f9_Prefix.operation,
    PV_STX2_SliceF4.node4,PV_STX2_SliceF4.node5,PV_STX2_SliceF4.node6,
    PV_FN_W2_LifetimePrefix.store,moved,write,consumed]

/-- Actual ArrayRepeat request and emitted cleanup, not a manufactured reply. -/
theorem issue {E : Type} (x : Input E) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 1
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.program.body.drop 7},
        x.parent :: x.parents,prepared x⟩,x.w,x.es⟩,x.stack⟩ = out x := by
  change PV_THR2_IntrinsicState.advance _ _ _ _ 1
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF4.node7 ::
      PV_STX2_SliceF4.program.body.drop 8},x.parent :: x.parents,prepared x⟩,x.w,x.es⟩,x.stack⟩ = _
  unfold PV_STX2_SliceF4.node7
  exact PV_FN_SLICE_f8_Prefix.issue _ x.K x.P x.H (prepared x) (consumed x) x.a
    (x.parent :: x.parents) (PV_STX2_SliceF4.program.body.drop 8) source.1
    kindGenerics.1 kindGenerics.2 [.move (.local 10)] [PV_FN_SLICE_f23.value]
    2 source.2.2 x.w x.es x.stack (operand x)

/-- The CLOSED provider supplies the returned operand through cells only.
This port admits a different activation counter, subject to the caller's
numbering invariant; no whole-store equality is required across f23. -/
theorem operand_from_post {E : Type} (x : Input E)
    (post : PV_FN_SLICE_f23.Post (PV_FN_SLICE_f4_Prefix.input23 x))
    (t : Store Data)
    (cells : t.cells = (PV_FN_SLICE_f23.finalStore (PV_FN_SLICE_f4_Prefix.input23 x)).cells) :
    t.cells ⟨x.a,11,[]⟩ = some PV_FN_SLICE_f23.value := by
  rw [cells]
  exact post.2.1

#print axioms run
#print axioms operand
#print axioms issue
#print axioms operand_from_post
end PV_FN_SLICE_f4_Repeat
