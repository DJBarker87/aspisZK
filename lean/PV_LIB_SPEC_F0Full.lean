import PV_LIB_SPEC_F1Full
import PV_FN_THREAD_f0Entry
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F0Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
/-- Original entry has no fabricated parent. The call variant below separately
covers every actual lower/suspended caller suffix at a normal function call. -/
structure Original where
  store : Store Data
  activation : Nat
  n : Nat
  closure : Data
  world : OWNER
  events : List Event

def rootEntry (i : Original) : State :=
  ⟨⟨.running ⟨{activation := i.activation,remaining := PV_THR2_F0.live.body},[],i.store⟩,
    i.world,i.events⟩,[]⟩
/-- This projection is used ONLY by entry-reference/footprint predicates.
Its dummy frame is never executed or imposed as an original-entry parent. -/
def referenceInput (i : Original) : PV_LIB_SPEC_Row.Input :=
  ⟨i.store,i.activation,[.number i.n,i.closure],{activation := 0,remaining := []},[],0,
    ⟨.child .null i.activation [.number i.n,i.closure],.child i.activation (.local 0),[]⟩,
    i.world,i.events,[]⟩

def Captures (w : OWNER) (n : Nat) (closure : Data) : Prop :=
  ∃ (F Task : Type) (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task),
    captures.n.val = n ∧
    PV_THR2_OrderedFamiliesEntryRefined.OrderedFamiliesEntryOwned' w captures closure

def PreRoot (r : Runtime) (i : Original) : Prop :=
  i.store.cells ⟨i.activation,1,[]⟩ = some (.number i.n) ∧
  i.store.cells ⟨i.activation,2,[]⟩ = some i.closure ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  RegisteredValidity i.world ∧ Numbered (rootEntry i) ∧
  ReferenceEntry r (referenceInput i) ∧ Captures i.world i.n i.closure

inductive Input where
  | call : PV_LIB_SPEC_Row.Input → Input
  | original : Original → Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec

def Pre (r : Runtime) : Input → Prop
  | .original i => PreRoot r i
  | .call i => PV_LIB_SPEC_Row.Pre PV_THR2_F0.live 2 r i ∧
    ∃ n closure, i.arguments = [.number n,closure] ∧ Captures i.world n closure

def RootFrame (r : Runtime) (i : Original) (q : State) : Prop :=
  let s := PV_W1_LeafBoundary.statusStore q.current.status
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed q.current.world s.nextActivation ∧
  Numbered q ∧ (∃ suffix, q.current.events = i.events ++ suffix) ∧
  ∀ p : Address, p.activation < i.activation →
    ¬ PV_W1_ArgumentEffects.Writable r.carrier
      (PV_LIB_SPEC_Row.leafEntry (referenceInput i)) i.world p → s.cells p = i.store.cells p

/-- Whole ordered-family output, at own completion/delivery, including both
worker/sequential routes and all resource/OS outcomes. No Some restriction. -/
def PostRoot (table : FullStoreActionTable) (r : Runtime) (i : Original)
    (candidate : Nat → State) : Prop :=
  let m := PV_LIB_SPEC_Full.source table r
  Behavior m (rootEntry i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ Boundary m (rootEntry i) candidate j) →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => RootFrame r i (candidate k)

def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  match i with
  | .original root => PostRoot table r root candidate
  | .call call => PV_LIB_SPEC_Full.Post table r PV_THR2_F0.live call candidate

def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)

/-- Literal package prefix: arbitrary caller entry to request16, not the
ordered-family return or an original-entry ownership theorem. -/
def PackageStatement : Prop := ∀ {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (n f flag : Data) (w : W) (es : List E) (stack : List Config),
    s.cells ⟨a,1,[]⟩ = some n → s.cells ⟨a,2,[]⟩ = some f →
    B.constant PV_THR2_RunEntryCall.flagDescriptor = some flag →
    PV_THR2_IntrinsicState.advance B K P H 6
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F0.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨PV_FN_THREAD_f0Entry.parent s a n f flag,parents,
        PV_FN_THREAD_f0Entry.issued s a n f flag⟩,w,es⟩,stack⟩

def Comparison (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PackageStatement ∧ Contract table r implementation
#print axioms Original
#print axioms rootEntry
#print axioms referenceInput
#print axioms Captures
#print axioms PreRoot
#print axioms Input
#print axioms MachineSpec
#print axioms Pre
#print axioms RootFrame
#print axioms PostRoot
#print axioms Post
#print axioms Contract
#print axioms PackageStatement
#print axioms Comparison
end PV_LIB_SPEC_F0Full
