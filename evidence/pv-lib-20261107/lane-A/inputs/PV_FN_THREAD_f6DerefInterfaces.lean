import PV_FN_THREAD_f6InterfaceSites
import PV_FN_THREAD_f6ParkDeref
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6DerefInterfaces
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces PV_FN_THREAD_f6InterfaceSites

inductive Site where
  | completion
  | park
  | finalCheck

def number : Site → Nat
  | .completion => 2097
  | .park => 2306
  | .finalCheck => 2659

def preStore (site : Site) (t : Store Data) (a : Nat) : Store Data :=
  match site with
  | .completion => write (PV_FN_THREAD_f6CompletionEntry.prepared t a) ⟨a,18,[]⟩ none
  | .park => write (PV_FN_THREAD_f6ParkDeref.prepared t a) ⟨a,23,[]⟩ none
  | .finalCheck => write (PV_FN_THREAD_f6FinalDerefRequest.prepared t a) ⟨a,31,[]⟩ none

def fn : Site → Data
  | .completion => PV_FN_THREAD_f6CompletionEntry.fn
  | .park => PV_FN_THREAD_f6ParkDeref.fn
  | .finalCheck => PV_FN_THREAD_f6FinalDerefRequest.fn

def dest : Site → Nat
  | .completion => 17
  | .park => 22
  | .finalCheck => 30

def rest : Site → List PV_STX2_SliceSyntax.Node
  | .completion => PV_THR2_F6.block86.drop 7
  | .park => PV_THR2_F6.block86.drop 24
  | .finalCheck => PV_THR2_F6.live.body.drop 62

def loops (site : Site) (saved : List LoopFrame) : List LoopFrame :=
  match site with
  | .completion => [⟨PV_THR2_F6.block86,PV_THR2_F6.live.body.drop 52⟩]
  | _ => saved

/-- Each126 entry binds the reference f6 created from its OWN Scope field.
The payload is absent here: it will be derived from124, then framed by125. -/
def input {E : Type} (site : Site) (t : Store Data) (a : Nat) (parents : List Frame)
    (saved : List LoopFrame) (w : OWNER) (es : List E) (stack : List Config) : Entry E :=
  one (preStore site t a) a parents (loops site saved) (rest site) (fn site)
    (PV_STX2_TypedReferences.reference ⟨a,2,[0]⟩ .null) (dest site) PV_THR2_F126.live w es stack

/-- The pending configurations are exactly those proved by f6's own segments.
Every distinct emitted126 descriptor is retained; no Packet-only instance. -/
def caller (site : Site) (t : Store Data) (a : Nat) (parents : List Frame)
    (saved : List LoopFrame) : Config :=
  match site with
  | .completion => PV_FN_THREAD_f6CompletionEntry.pending t a parents
  | .park => PV_FN_THREAD_f6ParkDeref.pending t a parents saved
  | .finalCheck => PV_FN_THREAD_f6FinalDerefRequest.pending t a parents saved

theorem actual_site {E : Type} (site : Site) (t : Store Data) (a : Nat) (parents : List Frame)
    (saved : List LoopFrame) (w : OWNER) (es : List E) (stack : List Config) :
    let x := input site t a parents saved w es stack
    let c := caller site t a parents saved
    x.parent = c.frame ∧ x.parents = c.callers ∧ x.store = c.store ∧
      x.activation = t.nextActivation := by
  cases site <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- Source-only writes preserve the activation counter, so entry validity
follows from the preceding dependency's OWNER Post at every126 site. -/
theorem valid {E : Type} (site : Site) (t : Store Data) (a : Nat) (parents : List Frame)
    (saved : List LoopFrame) (w : OWNER) (es : List E) (stack : List Config)
    (live : a < t.nextActivation) (owner : OwnerWellFormed w t.nextActivation) :
    EntryValid (input site t a parents saved w es stack) := by
  cases site <;> apply one_valid <;> assumption

/-- Same named dependency at2097,2306 and2659, instantiated at the actual
Scope reference and arbitrary ScopeData payload. The two Arc projections are
internal Pre obligations; deriving them from124/125 is still assembly work. -/
theorem at_scope_deref {E : Type} (M : Machine E) (thread_f126 : f126 M)
    (site : Site) (t : Store Data) (a : Nat) (parents : List Frame)
    (saved : List LoopFrame) (w : OWNER) (es : List E) (stack : List Config)
    (arc payload : Data) (live : a < t.nextActivation)
    (owner : OwnerWellFormed w t.nextActivation)
    (scopeAt : At M.carrier (input site t a parents saved w es stack).store ⟨a,2,[0]⟩ arc)
    (arcAt : ArcAt M.carrier (input site t a parents saved w es stack).store arc payload) :
    let x := input site t a parents saved w es stack
    FullPost M x (fun post _ result => ReadOnlyFrame x post ∧
      ∃ p strong weak, arc = PV_THR2_Packet124ReturnData.value
          (PV_STX2_TypedReferences.reference p .null) ∧
        At M.carrier post p (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
          [strong,weak,payload]) ∧
        result = PV_STX2_TypedReferences.reference {p with fields := p.fields ++ [2]} .null) := by
  exact thread_f126 _ ⟨a,2,[0]⟩ arc payload .null rfl rfl
    (valid site t a parents saved w es stack live owner) scopeAt arcAt

#print axioms actual_site
#print axioms valid
#print axioms at_scope_deref
end PV_FN_THREAD_f6DerefInterfaces
