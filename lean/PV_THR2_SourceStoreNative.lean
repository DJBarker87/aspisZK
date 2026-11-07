import PV_THR2_IntrinsicState
import PV_THR2_ExecutionBoundary
set_option autoImplicit false
namespace PV_THR2_SourceStoreNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- D959's complete direct source-reference writer inventory. These are
function identities, not source statement numbers (which native Waiting
does not retain). All eight emitted sites are recorded in session15. -/
inductive Function where
  | intoIterNext9 | vecAppend10 | rangeNext93 | vecPush167 | cellReplace289
  deriving DecidableEq

def function : Data → Option Function
  | .object [("Regular",.object [("kind",.object [("Fun",.object
      [("Regular",.number n)])]),("generics",_)])] =>
    match n with
    | 9 => some .intoIterNext9
    | 10 => some .vecAppend10
    | 93 => some .rangeNext93
    | 167 => some .vecPush167
    | 289 => some .cellReplace289
    | _ => none
  | _ => none

/-- A real store channel, separate from the unchanged full native reply.
Its five interpretations must be the named library meanings, not an identity
delta or a hypothesis asserting that the OLD machine performs a write.
This foundational module establishes dispatch/administration only. -/
abbrev Actions (W E : Type) := Function → Data → List Data → Store Data → W →
  Reply W E Data → Store Data

structure Site where
  meaning : Function
  callee : Data
  waiting : PV_STX2_Native.Waiting Data
  arguments : List Data

/-- Recognize only an ordinary pending native poll of a listed function.
Structured inline calls, completed frames and non-child requests are neutral.
The issued request itself identifies the leaf; no erased-value lookup is used. -/
def select (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) : Option Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn _ args =>
      match programs fn with
      | some _ => none
      | none =>
        let f ← function fn
        pure ⟨f,fn,wait,args⟩
    | _ => none

/-- NEW interpreter. The native action operates on the actual issued Store,
before the existing full reply rule. Neither the reply nor any world/event
projection is replaced. Pending stays waiting; failure, div and fault retain
their original administration. Intrinsic callback interception has priority.
No old interpreter or proved module is edited. -/
noncomputable def step {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (actions : Actions W E) (s : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.State W E :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_THR2_IntrinsicState.step C ctl programs H s
    | none => match select programs c with
      | none => PV_THR2_IntrinsicState.step C ctl programs H s
      | some site =>
        let reply := H site.waiting.request s.current.world
        let changed := {c with store := (actions site.meaning site.callee site.arguments
          c.store s.current.world reply)}
        let q := PV_THR2_ChildBoundary.delivered C changed site.waiting reply
        ⟨⟨q.status,q.world,s.current.events ++ q.events⟩,s.suspended⟩
  | _ => PV_THR2_IntrinsicState.step C ctl programs H s

noncomputable def advance {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (actions : Actions W E) : Nat → PV_THR2_IntrinsicState.State W E →
      PV_THR2_IntrinsicState.State W E
  | 0,s => s
  | n+1,s => advance C ctl programs H actions n (step C ctl programs H actions s)

/-- Exact all-answer native administration on the explicit final Store.
This does not assert that an arbitrary Actions parameter has source semantics. -/
theorem effects {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (actions : Actions W E) (c : Config) (w : W) (es : List E)
    (stack : List Config) (site : Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select programs c = some site) :
    let r := H site.waiting.request w
    let out := step C ctl programs H actions ⟨⟨.running c,w,es⟩,stack⟩
    out.current.world = r.world ∧ out.current.events = es ++ r.events ∧
      out.suspended = stack := by
  dsimp only
  simp only [step,ordinary,selected]
  have h := PV_THR2_ChildBoundary.effects C
    {c with store := (actions site.meaning site.callee site.arguments c.store w
      (H site.waiting.request w))} site.waiting (H site.waiting.request w)
  exact ⟨h.1,congrArg (es ++ ·) h.2,True.intro⟩

#print axioms function
#print axioms select
#print axioms step
#print axioms advance
#print axioms effects
end PV_THR2_SourceStoreNative
