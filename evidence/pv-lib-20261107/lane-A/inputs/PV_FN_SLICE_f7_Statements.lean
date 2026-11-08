import PV_FN_SLICE_f7_Into8
import PV_FN_SLICE_f7_AfterDrop
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_SLICE_f7_Prefix.Input
abbrev State (E : Type) := PV_THR2_IntrinsicState.State OWNER E
abbrev Outcome := PV_FN_SLICE_f8_FullReplies.Outcome
abbrev Effects := PV_FN_SLICE_f8_FullReplies.Effects
/-- Own-entry statements. The provider's representation is used literally.
Generator-domain and uniform-runtime obligations are not claimed by this file. -/
structure Pre {E : Type} (x : Input E) : Prop extends PV_FN_SLICE_f7_Prefix.Pre x where
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  source8 : x.P PV_FN_SLICE_f7_Prefix.source.2.1 = some PV_STX2_SliceF8.program
  source6 : x.P PV_FN_SLICE_f8_PrefixData.source.2.1 = some PV_STX2_SliceF6.program

def entry {E : Type} (x : Input E) : State E :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body},
    x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩
def after8 {E : Type} (x : Input E) (o : Outcome E) : State E :=
  PV_FN_SLICE_f8_FullReplies.finish (PV_FN_SLICE_f7_Prefix.input8 x) o
/-- Pending f8 at its ACTUAL call entry, using the provider Pre and Post
literally. The existing conditional provider theorem supplies this once its
own pending f6 dependency is supplied; f7 does not inspect that dependency. -/
def Callee8 {E : Type} (x : Input E) : Prop :=
  PV_FN_SLICE_f8.Pre (PV_FN_SLICE_f7_Prefix.input8 x) →
    PV_FN_SLICE_f8.Post (PV_FN_SLICE_f7_Prefix.input8 x)
def Through8 : Prop := ∀ {E : Type} (x : Input E), Pre x → Callee8 x →
  ∃ o : Outcome E,
    PV_FN_SLICE_f8_FullReplies.Executed6 (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
    ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
      (entry x) = after8 x o
/-- Exact successful f8 post-store, including the write to f7 LOCAL0. -/
def successStore {E : Type} (x : Input E) (v : Data) (d : Effects E) : Store Data :=
  PV_FN_SLICE_f8_Suffix.finalStore
    (PV_FN_SLICE_f8_FullReplies.suffix (PV_FN_SLICE_f7_Prefix.input8 x) v d)
def successInput {E : Type} (x : Input E) (v : Data) (d : Effects E) : PV_FN_THREAD_f315.Input E :=
  {x.toInput with s := successStore x v d,w := d.world,es := d.events,ptr := PV_FN_SLICE_f8_Suffix.value v}
def SuccessBoundary : Prop := ∀ {E : Type} (x : Input E) (v : Data) (d : Effects E),
  after8 x (.success v d) =
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4},
      x.parent :: x.parents,successStore x v d⟩,d.world,d.events⟩,x.stack⟩
def SuccessValue : Prop := ∀ {E : Type} (x : Input E) (v : Data) (d : Effects E),
  (successStore x v d).cells ⟨x.a,0,[]⟩ = some (PV_FN_SLICE_f8_Suffix.value v)
def Callee8From6 : Prop := ∀ {E : Type} (x : Input E),
  PV_FN_SLICE_f6Consumer.Contract (PV_FN_SLICE_f7_Prefix.input8 x) → Callee8 x
/-- Drop instruction issue, before any native answer or reachable Store delta. -/
def IssueDrop : Prop := ∀ {E : Type} (x : PV_FN_THREAD_f315.Input E) (capture : Data),
  x.s.cells ⟨x.a,1,[]⟩ = some capture →
  PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 1
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4},
      x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
    ⟨⟨.running (PV_FN_SLICE_f7_AfterDrop.config x capture),x.w,x.es⟩,x.stack⟩
/-- Delivery on the COMPLETE post-effect Store x.s; no identification with
any pre-effect Store is asserted by this local join. -/
def ReceiveDrop : Prop := ∀ {E : Type} (x : PV_FN_THREAD_f315.Input E) (capture : Data),
  PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 1
    ⟨⟨.running (PV_FN_SLICE_f7_AfterDrop.config x capture),x.w,x.es⟩,x.stack⟩ =
    PV_FN_SLICE_f7_AfterDrop.received x capture
      (x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w)
/-- Non-success BODY results receive only f7's own return administration.
Fault, undefined and pending configurations are retained literally. -/
def otherFinish {E : Type} (x : Input E) (o : Outcome E) : State E :=
  match o with
  | .failure e d =>
    ⟨PV_THR2_ChildBoundary.delivered (PV_FN_SLICE_ValueCarrier.carrier x.C)
      ⟨x.parent,x.parents,d.store⟩ x.wait ⟨.returned (.fail e),d.world,d.events⟩,x.stack⟩
  | .divergence d =>
    ⟨PV_THR2_ChildBoundary.delivered (PV_FN_SLICE_ValueCarrier.carrier x.C)
      ⟨x.parent,x.parents,d.store⟩ x.wait ⟨.returned .div,d.world,d.events⟩,x.stack⟩
  | _ => after8 x o

def OtherJoin : Prop := ∀ {E : Type} (x : Input E), Pre x →
  ∀ o : Outcome E, (∀ v d, o ≠ .success v d) →
  ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
    (after8 x o) = otherFinish x o
/-- The all-answer prefix, with a composed conclusion for EVERY
non-success provider outcome. No successful-only body execution is assumed. -/
def OtherComposition : Prop := ∀ {E : Type} (x : Input E), Pre x → Callee8 x →
  ∃ o : Outcome E,
    PV_FN_SLICE_f8_FullReplies.Executed6 (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
    (∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
      (entry x) = after8 x o) ∧
    ((∀ v d, o ≠ .success v d) →
      ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
        (entry x) = otherFinish x o)
/-- The successful BODY result must still be live after the FULL Drop delta.
This is an internal join to discharge, never an entry or native-reply premise. -/
def DropLive {E : Type} (x : Input E) (v : Data) (d : Effects E)
    (t : Store Data) : Prop :=
  t.cells ⟨x.a,0,[]⟩ = some (PV_FN_SLICE_f8_Suffix.value v)
/-- All-answer post-Drop join. Only a successful native answer needs the
live return-value read; errors/divergence never run the successful suffix. -/
def DropJoin : Prop := ∀ {E : Type} (x : PV_FN_THREAD_f315.Input E)
    (capture : Data) (r : Reply OWNER E Data),
  x.parent.waiting = some x.wait → x.wait.action = .child x.a (.local x.dest) →
  (match r.answer with
   | .returned (.ok _) => x.s.cells ⟨x.a,0,[]⟩ = some x.ptr ∧
       PV_W1_OwnerWellFormed.OwnerWellFormed r.world x.s.nextActivation
   | _ => True) →
  PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
    (PV_FN_SLICE_f7_AfterDrop.steps r) (PV_FN_SLICE_f7_AfterDrop.received x capture r) =
    PV_FN_SLICE_f7_AfterDrop.finish x capture r
/-- Own-source composition on an explicit Store. This statement makes no
claim that a native Store delta has been applied by the intrinsic runner. -/
def DropComposition : Prop := ∀ {E : Type} (x : PV_FN_THREAD_f315.Input E)
    (capture : Data),
  x.s.cells ⟨x.a,1,[]⟩ = some capture →
  x.parent.waiting = some x.wait → x.wait.action = .child x.a (.local x.dest) →
  let r := x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w
  (match r.answer with
   | .returned (.ok _) => x.s.cells ⟨x.a,0,[]⟩ = some x.ptr ∧
       PV_W1_OwnerWellFormed.OwnerWellFormed r.world x.s.nextActivation
   | _ => True) →
  PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
    (1+1+PV_FN_SLICE_f7_AfterDrop.steps r)
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4},
      x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
    PV_FN_SLICE_f7_AfterDrop.finish x capture r
/-- Caller frame stated at own entry. Native writes are restricted to the
argument-reachable roots; fresh activation cells stay explicit in the Store. -/
def Frame {E : Type} (x : Input E) (q : State E) : Prop :=
  let e : PV_W1_LeafBoundary.Entry :=
    {store := x.s,caller := x.a,parents := x.parent :: x.parents,loops := [],
      rest := [],callee := .null,arguments := [x.ptr,PV_FN_SLICE_f7_Prefix.tuple x],
      destination := x.dest,suspended := x.stack}
  ∀ p : Address, p.activation < x.s.nextActivation → p.activation ≠ x.a →
    p ≠ ⟨x.parent.activation,x.dest,[]⟩ →
    ¬ PV_W1_ArgumentEffects.Writable (PV_FN_SLICE_ValueCarrier.carrier x.C) e x.w p →
    (PV_FN_SLICE_f8.store q).cells p = x.s.cells p
/-- All-answer target with the actual callee outcome and both execution joins
bound to the SAME witness. The successful case exposes its full Drop Store,
actual request/reply, live result and saved continuation. W5 footprint
instantiation and actual runtime transport remain obligations, not hypotheses
hidden in this statement. -/
def Post {E : Type} (x : Input E) : Prop :=
  ∃ o : Outcome E,
    PV_FN_SLICE_f8_FullReplies.Executed6 (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
    PV_FN_SLICE_f8.Post (PV_FN_SLICE_f7_Prefix.input8 x) ∧
    PV_FN_SLICE_f8.PendingNative (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
    PV_FN_SLICE_f8.FirstOutcome (PV_FN_SLICE_f7_Prefix.input8 x) o ∧
    ∃ q : State E,
      (∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
        (entry x) = q) ∧ Frame x q ∧
      PV_W1_OwnerWellFormed.OwnerWellFormed q.current.world (PV_FN_SLICE_f8.store q).nextActivation ∧
      x.s.nextActivation ≤ (PV_FN_SLICE_f8.store q).nextActivation ∧
      (∃ suffix, q.current.events = x.es ++ suffix) ∧
      match o with
      | .success v d =>
        ∃ (capture : Data) (t : Store Data) (r : Reply OWNER E Data),
          (successStore x v d).cells ⟨x.a,1,[]⟩ = some capture ∧
          r = x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) d.world ∧
          (match r.answer with | .returned (.ok _) => DropLive x v d t | _ => True) ∧
          (∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
            (after8 x o) = PV_FN_SLICE_f7_AfterDrop.received
              {successInput x v d with s := t} capture r) ∧
          q = PV_FN_SLICE_f7_AfterDrop.finish {successInput x v d with s := t} capture r
      | _ => q = otherFinish x o

/-- Required own-entry theorem type; no proof or closure is asserted. -/
def Contract : Prop := ∀ {E : Type} (x : Input E), Pre x → Callee8 x → Post x

set_option pp.fullNames true in
set_option pp.proofs false in
#print Pre
set_option pp.fullNames true in
set_option pp.proofs false in
#print Post
#check Contract
#check SuccessBoundary
#check SuccessValue
#check Callee8From6
#check Callee8
#check Through8
#check OtherComposition
#check IssueDrop
#check ReceiveDrop
#check OtherJoin
#check DropLive
#check DropJoin
#check DropComposition
end PV_FN_SLICE_f7
