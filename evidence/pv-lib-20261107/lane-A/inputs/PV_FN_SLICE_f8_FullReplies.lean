import PV_FN_SLICE_f8_Prefix
import PV_FN_SLICE_f8_Suffix
import PV_FN_W2_BinaryReturnOutcome
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f8_FullReplies
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_SLICE_f8_PrefixData.Input
abbrev State (E : Type) := PV_THR2_IntrinsicState.State OWNER E
structure Effects (E : Type) where
  store : Store Data
  world : OWNER
  events : List E
/-- A full BODY reply, not a native Reply pasted onto the old store. Pending
carries its actual internal waiting configuration and suspended stack. -/
inductive Outcome (E : Type) where
  | success (value : Data) (effects : Effects E)
  | failure (error : Error) (effects : Effects E)
  | divergence (effects : Effects E)
  | fault (reason : Fault) (effects : Effects E)
  | undefined (site : Option Site) (effects : Effects E)
  | pending (state : State E)
structure Pre {E : Type} (x : Input E) : Prop extends PV_FN_SLICE_f8_PrefixData.Pre x where
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)

def suffix {E : Type} (x : Input E) (v : Data) (d : Effects E) : PV_FN_SLICE_f8_Suffix.Input E :=
  {x.toInput with s := d.store,w := d.world,es := d.events,ptr := v}
def held {E : Type} (x : Input E) : PV_STX2_Native.Waiting Data :=
  ⟨.child PV_FN_SLICE_f8_PrefixData.source.2.1 x.s.nextActivation
    [PV_FN_SLICE_f8_PrefixData.generator x,PV_FN_SLICE_f8_PrefixData.tuple x.index],
    .child x.s.nextActivation (.local 4),PV_FN_SLICE_f8_PrefixData.source.2.2.2.2⟩
def completed {E : Type} (x : Input E) (r : Result Data) (d : Effects E) : State E :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop 9,waiting := some (held x),completed := some r},x.parent :: x.parents,d.store⟩,d.world,d.events⟩,x.stack⟩
def boundary {E : Type} (x : Input E) : Outcome E → State E
  | .success v d => ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body.drop 9},
      x.parent :: x.parents,d.store⟩,d.world,d.events⟩,x.stack⟩
  | .failure error d => completed x (.fail error) d
  | .divergence d => completed x .div d
  | .fault reason d => ⟨⟨.fault reason d.store,d.world,d.events⟩,x.stack⟩
  | .undefined site d => ⟨⟨.undefined site d.store,d.world,d.events⟩,x.stack⟩
  | .pending q => q

def deliver {E : Type} (x : Input E) (r : Result Data) (d : Effects E) : State E :=
  ⟨PV_THR2_ChildBoundary.delivered (PV_FN_SLICE_ValueCarrier.carrier x.C)
    ⟨x.parent,x.parents,d.store⟩ x.wait ⟨.returned r,d.world,d.events⟩,x.stack⟩
def finish {E : Type} (x : Input E) : Outcome E → State E
  | .success v d => ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,
      PV_FN_SLICE_f8_Suffix.finalStore (suffix x v d)⟩,d.world,d.events⟩,x.stack⟩
  | .failure error d => deliver x (.fail error) d
  | .divergence d => deliver x .div d
  | other => boundary x other

def steps {E : Type} : Outcome E → Nat
  | .success _ _ => 9
  | .failure _ _ | .divergence _ => 1
  | _ => 0
/-- INTERNAL success-boundary information. This is supplied by the actual
callee's successful Post, never assumed at f8 call entry. -/
def Returned {E : Type} (x : Input E) : Outcome E → Prop
  | .success v d => d.store.cells ⟨x.a,4,[]⟩ = some v ∧
      PV_W1_OwnerWellFormed.OwnerWellFormed d.world d.store.nextActivation
  | _ => True

/-- Join only f8's own source after an arbitrary full callee outcome. Every
fault/undefined/pending state is preserved literally. Result failure and div
receive one outer return step; they never run the successful suffix. -/
theorem after {E : Type} (x : Input E) (pre : Pre x) (o : Outcome E) (returned : Returned x o) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
      (steps o) (boundary x o) = finish x o := by
  cases o with
  | success v d =>
    exact PV_FN_SLICE_f8_Suffix.run (suffix x v d)
      ⟨returned.1,pre.saved,pre.action,returned.2⟩
  | failure error d =>
    exact PV_FN_W2_BinaryReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
      x.K x.P x.H d.store x.a x.dest (PV_STX2_SliceF8.program.body.drop 9) []
      x.parent x.parents x.wait (held x) (.fail error)
      PV_FN_SLICE_f8_PrefixData.source.2.1 (PV_FN_SLICE_f8_PrefixData.generator x)
      (PV_FN_SLICE_f8_PrefixData.tuple x.index) x.s.nextActivation d.world d.events x.stack
      pre.saved pre.action rfl
  | divergence d =>
    exact PV_FN_W2_BinaryReturnOutcome.completed (PV_FN_SLICE_ValueCarrier.carrier x.C)
      x.K x.P x.H d.store x.a x.dest (PV_STX2_SliceF8.program.body.drop 9) []
      x.parent x.parents x.wait (held x) .div
      PV_FN_SLICE_f8_PrefixData.source.2.1 (PV_FN_SLICE_f8_PrefixData.generator x)
      (PV_FN_SLICE_f8_PrefixData.tuple x.index) x.s.nextActivation d.world d.events x.stack
      pre.saved pre.action rfl
  | fault reason d => rfl
  | undefined site d => rfl
  | pending q => rfl

/-- A pending full BODY contract must provide the actual executed run from
the issued source195 call, not a native-only reply or a post-store replacement.
This local interface has not yet discharged the f6 entry-domain, native wait
provenance, full frame and uniform OWNER-interpreter linkage obligations. -/
def Executed6 {E : Type} (x : Input E) (o : Outcome E) : Prop :=
  Returned x o ∧ ∃ n, PV_THR2_IntrinsicState.advance
    (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
    (PV_FN_SLICE_f8_PrefixData.out x) = boundary x o

/-- Own-entry all-outcome composition. A source BODY dependency remains an
explicit argument; this theorem alone is NOT a B-y row closure. -/
theorem run {E : Type} (x : Input E) (pre : Pre x) (o : Outcome E) (callee6 : Executed6 x o) :
    ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = finish x o := by
  obtain ⟨returned,n,body⟩ := callee6
  refine ⟨9+n+steps o,?_⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_SLICE_f8_Prefix.run x pre.toPre,body]
  exact after x pre o returned
#print axioms after
#print axioms run
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print run
end PV_FN_SLICE_f8_FullReplies
