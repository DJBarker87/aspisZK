import PV_FN_SLICE_f7_Suffix
import PV_FN_W2_DropReturnOutcome
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_AfterDrop
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input
abbrev State (E : Type) := PV_THR2_IntrinsicState.State OWNER E
/-- This is an INTERNAL native full-post-store boundary. When composing f7,
W5's closed Drop contract must discharge its owner/frame conclusions here. -/
structure Pre {E : Type} (x : Input E) (r : Reply OWNER E Data) : Prop where
  value : x.s.cells ⟨x.a,0,[]⟩ = some x.ptr
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  owner : PV_W1_OwnerWellFormed.OwnerWellFormed r.world x.s.nextActivation

def source : Data × List Instruction := match PV_STX2_SliceF7.node4 with
  | .leaf (.drop _ _ fn _ cleanup) => (fn,cleanup)
  | _ => (.null,[])
def waiting (capture : Data) : PV_STX2_Native.Waiting Data :=
  ⟨.drop source.1 capture,.dropped (.local 1),source.2⟩
def config {E : Type} (x : Input E) (capture : Data) : Config :=
  ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 5,waiting := some (waiting capture)},
    x.parent :: x.parents,x.s⟩
/-- The arbitrary native Store delta has ALREADY been applied in x.s. Neither
success, failure nor pending is delivered on a previous source Store. -/
def received {E : Type} (x : Input E) (capture : Data) (r : Reply OWNER E Data) : State E :=
  let p := PV_THR2_ChildBoundary.delivered (PV_FN_SLICE_ValueCarrier.carrier x.C)
    (config x capture) (waiting capture) r
  ⟨{p with events := x.es ++ p.events},x.stack⟩
def suffix {E : Type} (x : Input E) (r : Reply OWNER E Data) : Input E :=
  {x with s := write x.s ⟨x.a,1,[]⟩ none,w := r.world,es := x.es ++ r.events}
def completed {E : Type} (x : Input E) (capture : Data) (result : Result Data)
    (r : Reply OWNER E Data) : State E :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 5,waiting := some (waiting capture),completed := some result},
    x.parent :: x.parents,x.s⟩,r.world,x.es ++ r.events⟩,x.stack⟩
def boundary {E : Type} (x : Input E) (capture : Data) (r : Reply OWNER E Data) : State E :=
  match r.answer with
  | .returned (.ok _) =>
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 5},
      x.parent :: x.parents,(suffix x r).s⟩,r.world,x.es ++ r.events⟩,x.stack⟩
  | .returned result => completed x capture result r
  | _ => received x capture r

def finish {E : Type} (x : Input E) (capture : Data) (r : Reply OWNER E Data) : State E :=
  match r.answer with
  | .returned (.ok _) =>
    ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,
      PV_FN_SLICE_f7_Suffix.finalStore (suffix x r)⟩,r.world,x.es ++ r.events⟩,x.stack⟩
  | .returned result =>
    ⟨PV_THR2_ChildBoundary.delivered (PV_FN_SLICE_ValueCarrier.carrier x.C)
      ⟨x.parent,x.parents,x.s⟩ x.wait ⟨.returned result,r.world,x.es ++ r.events⟩,x.stack⟩
  | _ => received x capture r

def steps {E : Type} (r : Reply OWNER E Data) : Nat :=
  match r.answer with
  | .returned (.ok _) => 5
  | .returned _ => 1
  | _ => 0

/-- Frozen native delivery, including exact dropped-place invalidation,
source cleanup payload, pinned panic strategy and still-running pending. -/
theorem received_eq {E : Type} (x : Input E) (capture : Data) (r : Reply OWNER E Data) :
    received x capture r = boundary x capture r := by
  cases r with
  | mk answer w events =>
    cases answer with
    | pending => rfl
    | fault f => rfl
    | returned result =>
      cases result <;>
        simp [received,boundary,completed,suffix,config,waiting,
          PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
          PV_STX2_Native.reply,PV_STX2_Native.storeResult,native,adopt,locate,writeAddress]

/-- All native answers at178: successful drop runs only f7's own source
suffix; errors/divergence return once; fault and pending remain EXACTLY as
received. This is a local full-reply stage, not the entire f7 contract. -/
theorem run {E : Type} (x : Input E) (capture : Data) (r : Reply OWNER E Data) (pre : Pre x r) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
      (steps r) (received x capture r) = finish x capture r := by
  rw [received_eq]
  cases r with
  | mk answer w events =>
    cases answer with
    | pending => rfl
    | fault f => rfl
    | returned result =>
      cases result with
      | ok ignored =>
        apply PV_FN_SLICE_f7_Suffix.run (suffix x ⟨.returned (.ok ignored),w,events⟩)
        refine ⟨?_,pre.saved,pre.action,pre.owner⟩
        have different : (⟨x.a,0,[]⟩ : Address) ≠ ⟨x.a,1,[]⟩ := by
          intro equal
          have bad := congrArg Address.localIndex equal
          change 0 = 1 at bad
          omega
        simpa only [suffix,write,if_neg different] using pre.value
      | fail error =>
        exact PV_FN_W2_DropReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
          x.K x.P x.H x.s x.a x.dest (PV_STX2_SliceF7.program.body.drop 5) []
          x.parent x.parents x.wait (waiting capture) (.fail error) source.1 capture
          w (x.es ++ events) x.stack pre.saved pre.action rfl
      | div =>
        exact PV_FN_W2_DropReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
          x.K x.P x.H x.s x.a x.dest (PV_STX2_SliceF7.program.body.drop 5) []
          x.parent x.parents x.wait (waiting capture) .div source.1 capture
          w (x.es ++ events) x.stack pre.saved pre.action rfl
#print axioms received_eq
#print axioms run
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print run
end PV_FN_SLICE_f7_AfterDrop
