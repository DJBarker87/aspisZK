import PV_FN_SLICE_f8_FullReplies
import PV_STX2_SliceF6
import PV_W1_ArgumentEffects
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f8
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_SLICE_f8_FullReplies
abbrev Input := PV_FN_SLICE_f8_FullReplies.Input
structure Pre {E : Type} (x : Input E) : Prop extends toFull : PV_FN_SLICE_f8_FullReplies.Pre x where
  source6 : x.P PV_FN_SLICE_f8_PrefixData.source.2.1 = some PV_STX2_SliceF6.program

def store {E : Type} (q : State E) : Store Data := PV_W1_LeafBoundary.statusStore q.current.status
/-- Only pre-existing cells outside this frame, the return destination and
argument-reachable roots. Fresh child cells remain in the explicit full store. -/
def Frame {E : Type} (x : Input E) (q : State E) : Prop :=
  ∀ p : Address, p.activation < x.s.nextActivation → p.activation ≠ x.a →
    p ≠ ⟨x.parent.activation,x.dest,[]⟩ →
    ¬ PV_W1_ArgumentEffects.Writable (PV_FN_SLICE_ValueCarrier.carrier x.C)
      (PV_FN_SLICE_f8_PrefixData.entry6 x) x.w p → (store q).cells p = x.s.cells p

/-- Full callee output obligations; the native world and its observable events
are explicit, rather than replaced by entry state. Provider-native footprint
clauses remain inside the pending provider contract. -/
def CalleeFrame {E : Type} (x : Input E) (o : Outcome E) : Prop :=
  Frame x (boundary x o) ∧
  PV_W1_OwnerWellFormed.OwnerWellFormed (boundary x o).current.world (store (boundary x o)).nextActivation ∧
  x.s.nextActivation ≤ (store (boundary x o)).nextActivation ∧
  (boundary x o).suspended = x.stack ∧
  ∃ suffix, (boundary x o).current.events = x.es ++ suffix

/-- A pending witness identifies the ACTUAL native attempt and its immediate
post-state. Merely reaching a BODY call or its later native call is insufficient.
No transition after that pending reply is used by this witness. -/
def PendingNative {E : Type} (x : Input E) : Outcome E → Prop
  | .pending q => ∃ (n : Nat) (c : Config) (w : OWNER) (es : List E)
      (stack : List Config) (wait : PV_STX2_Native.Waiting Data),
      PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
        (PV_FN_SLICE_f8_PrefixData.out x) = ⟨⟨.running c,w,es⟩,stack⟩ ∧
      c.frame.waiting = some wait ∧ c.frame.completed = none ∧
      (match wait.request with | .child fn _ _ => x.P fn = none | _ => True) ∧
      (x.H wait.request w).answer = .pending ∧
      PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 1
        ⟨⟨.running c,w,es⟩,stack⟩ = q
  | _ => True

/-- Classify a native pending attempt in the reached state, before consuming
its reply. BODY requests are excluded by their resolver, and completed frames
are excluded because they perform return administration instead. -/
def NativePendingAt {E : Type} (x : Input E) (q : State E) : Prop :=
  ∃ (c : Config) (wait : PV_STX2_Native.Waiting Data),
    q.current.status = .running c ∧ c.frame.waiting = some wait ∧
    c.frame.completed = none ∧
    (match wait.request with | .child fn _ _ => x.P fn = none | _ => True) ∧
    (x.H wait.request q.current.world).answer = .pending
/-- Stop before crossing a previously pending reply. The common fuel belongs
to the same actual body run used for the outcome, not an unrelated witness. -/
def FirstOutcome {E : Type} (x : Input E) (o : Outcome E) : Prop :=
  ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
      (PV_FN_SLICE_f8_PrefixData.out x) = boundary x o ∧
    (∀ k, k+1 < n → ¬ NativePendingAt x
      (PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H k
        (PV_FN_SLICE_f8_PrefixData.out x))) ∧
    (match o with
     | .pending _ => ∃ k, n = k+1 ∧ NativePendingAt x
         (PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H k
           (PV_FN_SLICE_f8_PrefixData.out x))
     | _ => ∀ k, k < n → ¬ NativePendingAt x
         (PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H k
           (PV_FN_SLICE_f8_PrefixData.out x)))

/-- Complete own-store frame for the SUCCESS suffix on a complete callee store. -/
theorem success_frame {E : Type} (x : Input E) (v : Data) (d : Effects E)
    (frame : Frame x (boundary x (.success v d))) : Frame x (finish x (.success v d)) := by
  intro p older own destination outside
  exact (PV_FN_SLICE_f8_Suffix.frame (suffix x v d) p own destination).trans
    (frame p older own destination outside)

/-- Result errors and divergence do not write any extra source-store cell. -/
theorem error_store {E : Type} (x : Input E) (r : Result Data) (d : Effects E)
    (error : ∀ v, r ≠ .ok v) : store (deliver x r d) = d.store := by
  cases r with
  | ok v => exact False.elim (error v rfl)
  | fail e =>
    cases hp : x.parents <;>
      simp [store,deliver,PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,
        PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,native,adopt,
        PV_W1_LeafBoundary.statusStore,hp]
  | div =>
    cases hp : x.parents <;>
      simp [store,deliver,PV_THR2_ChildBoundary.delivered,PV_STX2_Pinned.reply,
        PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,native,adopt,
        PV_W1_LeafBoundary.statusStore,hp]

theorem finish_frame {E : Type} (x : Input E) (o : Outcome E)
    (frame : Frame x (boundary x o)) : Frame x (finish x o) := by
  cases o with
  | success v d => exact success_frame x v d frame
  | failure e d =>
    unfold Frame at frame ⊢
    rw [show store (finish x (.failure e d)) = d.store from error_store x (.fail e) d (by intros; intro h; cases h)]
    exact frame
  | divergence d =>
    unfold Frame at frame ⊢
    rw [show store (finish x (.divergence d)) = d.store from error_store x .div d (by intros; intro h; cases h)]
    exact frame
  | fault reason d => exact frame
  | undefined site d => exact frame
  | pending q => exact frame

theorem finish_effects {E : Type} (x : Input E) (o : Outcome E) :
    (finish x o).current.world = (boundary x o).current.world ∧
    (finish x o).current.events = (boundary x o).current.events ∧
    (store (finish x o)).nextActivation = (store (boundary x o)).nextActivation := by
  cases o with
  | success v d => exact ⟨rfl,rfl,rfl⟩
  | failure e d =>
    have effects := PV_THR2_ChildBoundary.effects (PV_FN_SLICE_ValueCarrier.carrier x.C)
      ⟨x.parent,x.parents,d.store⟩ x.wait (⟨.returned (.fail e),d.world,d.events⟩ : Reply OWNER E Data)
    exact ⟨effects.1,effects.2,congrArg Store.nextActivation (error_store x (.fail e) d (by intros; intro h; cases h))⟩
  | divergence d =>
    have effects := PV_THR2_ChildBoundary.effects (PV_FN_SLICE_ValueCarrier.carrier x.C)
      ⟨x.parent,x.parents,d.store⟩ x.wait (⟨.returned .div,d.world,d.events⟩ : Reply OWNER E Data)
    exact ⟨effects.1,effects.2,congrArg Store.nextActivation (error_store x .div d (by intros; intro h; cases h))⟩
  | fault reason d => exact ⟨rfl,rfl,rfl⟩
  | undefined site d => exact ⟨rfl,rfl,rfl⟩
  | pending q => exact ⟨rfl,rfl,rfl⟩
end PV_FN_SLICE_f8
namespace PV_FN_SLICE_f6Consumer
open PV_FN_SLICE_f8_FullReplies
/-- Named thread-17 pending interface at the actual source195 boundary.
A provider implication and the uniform OWNER runtime bridge remain required.
No provider representation is restated here. -/
def Contract {E : Type} (x : Input E) : Prop :=
  ∃ o : Outcome E, Executed6 x o ∧ PV_FN_SLICE_f8.CalleeFrame x o ∧ PV_FN_SLICE_f8.PendingNative x o ∧ PV_FN_SLICE_f8.FirstOutcome x o
end PV_FN_SLICE_f6Consumer
namespace PV_FN_SLICE_f8
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_SLICE_f8_FullReplies

def Post {E : Type} (x : Input E) : Prop :=
  ∃ o : Outcome E, Executed6 x o ∧ PendingNative x o ∧ FirstOutcome x o ∧
    (∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF8.program.body},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ = finish x o) ∧
    Frame x (finish x o) ∧
    PV_W1_OwnerWellFormed.OwnerWellFormed (finish x o).current.world (store (finish x o)).nextActivation ∧
    (finish x o).current.world = (boundary x o).current.world ∧
    (finish x o).current.events = (boundary x o).current.events ∧
    x.s.nextActivation ≤ (store (finish x o)).nextActivation

def Contract : Prop := ∀ {E : Type} (x : Input E),
  Pre x → PV_FN_SLICE_f6Consumer.Contract x → Post x
/-- Conditional own-entry contract. The pending provider must prove its full
contract implies the named interface, including genuine pending provenance.
This does not claim a uniform OWNER interpreter transport or provider closure. -/
theorem contract {E : Type} (x : Input E) (pre : Pre x)
    (callee6 : PV_FN_SLICE_f6Consumer.Contract x) : Post x := by
  obtain ⟨o,executed,frame,pending,first⟩ := callee6
  have effects := finish_effects x o
  refine ⟨o,executed,pending,first,PV_FN_SLICE_f8_FullReplies.run x pre.toFull o executed,
    finish_frame x o frame.1,?_,effects.1,effects.2.1,?_⟩
  · rw [effects.1,effects.2.2]
    exact frame.2.1
  · rw [effects.2.2]
    exact frame.2.2.1
#print axioms success_frame
#print axioms error_store
#print axioms finish_frame
#print axioms finish_effects
#print axioms contract
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print contract
end PV_FN_SLICE_f8
