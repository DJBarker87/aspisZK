import PV_LIB_A_V2F124Entry14
import PV_FN_THREAD_f6Provider124Entry
import PV_LIB_Arc124
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F124EntryData14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_FN_THREAD_f6Interfaces
open PV_LIB_A_V2F124Entry14 PV_LIB_A_StructuredFrontier13
abbrev Event := PV_RJ4IDB.NativeEvent

def input (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List Event) (stack : List Config) : Entry Event :=
  let parent := PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest (fn src) [payload] 3
  ⟨s.nextActivation,PV_THR2_F124.live,parent.store,parent.frame,parents,
    PV_THR2_StaticReply.wait s (fn src) [payload] 3,3,[payload],w,es,stack⟩

/-- The selected provider entry is exactly the actual source push, not a
fabricated child activation, parent, argument payload or post-call store. -/
theorem provenance (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List Event) (stack : List Config) :
    entry (input s a parents loops payload w es stack) =
      ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.entered s a parents loops rest (fn src) [payload] 3 PV_THR2_F124.live),w,es⟩,stack⟩ := rfl

theorem valid (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List Event) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w s.nextActivation) :
    EntryValid (input s a parents loops payload w es stack) := by
  refine ⟨PV_LIB_A_CallNumbers13.issued_counter s [payload],live,rfl,rfl,⟨fn src,rfl⟩,owner,?_⟩
  intro i v argument
  cases i with
  | zero =>
    simp [input] at argument
    subst v
    exact write_same {s with nextActivation := s.nextActivation+1} ⟨s.nextActivation,1,[]⟩ (some payload)
  | succ i => simp [input] at argument

theorem bounded (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List Event) (stack : List Config)
    (live : a < s.nextActivation)
    (lower : PV_STX2_LiveNumbering.StackBelow s.nextActivation a parents)
    (suspended : ∀ c ∈ stack, ∀ f ∈ c.frame :: c.callers, f.activation < s.nextActivation) :
    PV_FN_THREAD_f6Provider124Entry.StackBounded (input s a parents loops payload w es stack) := by
  constructor
  · intro f member
    change f.activation < (PV_THR2_StaticCall.issued s [payload]).nextActivation
    rw [PV_LIB_A_CallNumbers13.issued_counter]
    have age := PV_STX2_LiveNumbering.caller_older lower f member
    omega
  · intro c member f frame
    change f.activation < (PV_THR2_StaticCall.issued s [payload]).nextActivation
    rw [PV_LIB_A_CallNumbers13.issued_counter]
    exact Nat.lt_trans (suspended c member f frame) (Nat.lt_succ_self _)

/-- Instantiate CLOSED124's literal Pre from the actual issued entry's current
numbering/OWNER invariant. No count, alias, successful allocation or future
read is a premise. These are caller invariant projections to derive in the
original-entry join, not additional endpoint assumptions. -/
theorem pre (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W1_OwnerNativeFrame.Backend Event)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List Event) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w s.nextActivation)
    (lower : PV_STX2_LiveNumbering.StackBelow s.nextActivation a parents)
    (suspended : ∀ c ∈ stack, ∀ f ∈ c.frame :: c.callers, f.activation < s.nextActivation) :
    PV_FN_THREAD_f124.Pre (PV_FN_THREAD_f6Provider124Entry.convert C b K P H
      (input s a parents loops payload w es stack) payload) :=
  PV_FN_THREAD_f6Provider124Entry.pre C b K P H _ payload
    (valid s a parents loops payload w es stack live owner) rfl
    (bounded s a parents loops payload w es stack live lower suspended)

/-- CLOSED124 is applied BY NAME, keeping its FULL branch graph and explicit
Post store. This is a provider-model result. Its actual Full/v2/context/physical
transport is still required; no total byte image is re-credited here. -/
theorem installed (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W1_OwnerNativeFrame.Backend Event)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List Event) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w s.nextActivation)
    (lower : PV_STX2_LiveNumbering.StackBelow s.nextActivation a parents)
    (suspended : ∀ c ∈ stack, ∀ f ∈ c.frame :: c.callers, f.activation < s.nextActivation) :
    let x := PV_FN_THREAD_f6Provider124Entry.convert C b K P H (input s a parents loops payload w es stack) payload
    ∃ out, PV_FN_THREAD_f124.Reached x H resources encode shape out ∧
      PV_LIB_Arc124.law x H resources encode shape (PV_LIB.observe out) :=
  PV_LIB_Arc124.installed _ H resources encode shape
    (pre C b K P H s a parents loops payload w es stack live owner lower suspended)

#print axioms provenance
#print axioms valid
#print axioms bounded
#print axioms pre
#print axioms installed
end PV_LIB_A_F124EntryData14
