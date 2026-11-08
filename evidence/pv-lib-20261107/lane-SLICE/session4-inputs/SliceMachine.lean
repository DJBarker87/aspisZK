import PV_STX2_SliceSyntax
import PV_STX2_PinnedRun
import PV_STX2_ChainCaptures
set_option autoImplicit false
namespace PV_STX2_SliceMachine
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax

/-- Conditional on owner acceptance of the translator patch. A loop delimiter
retains the actual generated body and its caller's remaining instructions. -/
structure LoopFrame where
  body : List Node
  afterLoop : List Node

/-- Conditional on owner acceptance of the translator patch. A source activation
keeps its saved native child request; retry never allocates another activation. -/
structure Frame where
  activation : Nat
  remaining : List Node
  loops : List LoopFrame := []
  waiting : Option (PV_STX2_Native.Waiting Data) := none
  unwinding : Option Fault := none
  completed : Option (Result Data) := none

/-- Conditional on owner acceptance of the translator patch. All synchronous
children share the same source store, including their writes through captures. -/
structure Config where
  frame : Frame
  callers : List Frame
  store : Store Data

/-- Conditional on owner acceptance of the translator patch. Terminal states
retain the native store; an interpretation gap is distinct from source div. -/
inductive Status where
  | running (config : Config)
  | returned (result : Result Data) (store : Store Data)
  | fault (fault : Fault) (store : Store Data)
  | undefined (site : Option Site) (store : Store Data)

/-- Conditional on owner acceptance of the translator patch. World and event
prefix come from this single run, including failure and pending answers. -/
structure Prefix (W E : Type) where
  status : Status
  world : W
  events : List E

/-- Conditional on owner acceptance of the translator patch. Source enum-tag
interpretation remains explicit until installed from the actual aggregates. -/
structure Control where
  variant : Data → Option Nat
  binary : Data → Data → Data → Option Data

/-- Conditional on owner acceptance of the translator patch. Source entry
allocates a fresh activation and binds captures in their source operand order. -/
def enter (p : PV_STX2_SliceSyntax.Program) (captures : List Data) (s : Store Data) : Config :=
  let a := s.nextActivation
  ⟨{activation := a,remaining := p.body},[],PV_STX2_Native.arguments a captures 1 {s with nextActivation := a+1}⟩

/-- Conditional on owner acceptance of the translator patch. The old native
leaf evaluator is reused with the same activation, store and saved request. -/
def native (c : Config) (instructions : List Instruction) : PV_STX2_Native.Config Data :=
  ⟨c.frame.activation,instructions,c.store,c.frame.waiting,c.frame.unwinding⟩

/-- Conditional on owner acceptance of the translator patch. A successful
nested return retains its actual store until its parent's saved return binding. -/
def adopt {W E : Type} (c : Config) (rest : List Node)
    (p : PV_STX2_Native.Prefix W E Data) : Prefix W E :=
  let status := match p.status with
    | .running d => .running {c with store := d.store,frame :=
        {c.frame with remaining := rest,waiting := d.waiting,unwinding := d.unwinding}}
    | .returned r => match c.callers with
        | [] => .returned r c.store
        | _ :: _ => .running {c with frame := {c.frame with completed := some r}}
    | .fault f => .fault f c.store
    | .undefined site => .undefined site c.store
  ⟨status,p.world,p.events⟩

/-- Conditional on owner acceptance of the translator patch. Match arms are
selected by their emitted variant identifiers; missing variants stay gaps. -/
def selectVariant (n : Nat) : List (List Nat × List Node) → Option (List Node) →
    Option (List Node)
  | [], otherwise => otherwise
  | (keys,body) :: rest, otherwise =>
      if n ∈ keys then some body else selectVariant n rest otherwise

/-- Conditional on owner acceptance of the translator patch. Integer switch
keys use the same carrier interpretation as the previous native evaluator. -/
def selectKey {W : Type} (carrier : Carrier W Data) (value : Data) :
    List (List Data × List Node) → List Node → List Node
  | [], otherwise => otherwise
  | (keys,body) :: rest, otherwise =>
      if keys.any (carrier.matchesKey value) then body else selectKey carrier value rest otherwise

/-- Conditional on owner acceptance of the translator patch. One executed
transition, including call-stack entry and return administration. Generated
children reuse the activation already allocated by the emitted call leaf.
Opaque and intrinsic children use arbitrary full native replies. -/
def step {W E : Type} (carrier : Carrier W Data) (control : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) : Prefix W E := Id.run do
  let running (d : Config) : Prefix W E := ⟨.running d,w,[]⟩
  let gap (site : Option Site) : Prefix W E := ⟨.undefined site c.store,w,[]⟩
  if let some result := c.frame.completed then
    match c.callers with
    | [] => return ⟨.returned result c.store,w,[]⟩
    | parent :: rest =>
      let d := {c with frame := parent,callers := rest}
      match parent.waiting with
      | none => return gap none
      | some waiting => return (adopt d parent.remaining
          (PV_STX2_Pinned.reply carrier (native d []) waiting ⟨.returned result,w,[]⟩))
  if let some waiting := c.frame.waiting then
    if let .child callee activation _ := waiting.request then
      if let some program := programs callee then
        return running {c with
          frame := {activation := activation,remaining := program.body}
          callers := c.frame :: c.callers}
    return (adopt c c.frame.remaining
      (PV_STX2_Pinned.reply carrier (native c []) waiting (handler waiting.request w)))
  match c.frame.remaining with
  | [] => return gap none
  | node :: rest =>
    let next := {c with frame := {c.frame with remaining := rest}}
    match node with
    | .leaf instruction => return (adopt c rest
        (PV_STX2_Native.step carrier handler (native c [instruction]) w))
    | .loop _ body => return running {next with frame := {next.frame with
        remaining := body,loops := ⟨body,rest⟩ :: c.frame.loops}}
    | .breakLoop site depth =>
      match c.frame.loops[depth]? with
      | none => return gap (some site)
      | some target => return running {next with frame := {next.frame with
          remaining := target.afterLoop,loops := c.frame.loops.drop (depth+1)}}
    | .continueLoop site depth =>
      match c.frame.loops[depth]? with
      | none => return gap (some site)
      | some target => return running {next with frame := {next.frame with
          remaining := target.body,loops := c.frame.loops.drop depth}}
    | .branch site condition yes no =>
      match operand carrier c.store w c.frame.activation condition with
      | none => return gap (some site)
      | some (value,s) => match carrier.truth value with
          | none => return gap (some site)
          | some b => return running {next with store := s,frame :=
              {next.frame with remaining := (if b then yes else no) ++ rest}}
    | .switch site condition arms otherwise =>
      match operand carrier c.store w c.frame.activation condition with
      | none => return gap (some site)
      | some (value,s) => return running {next with store := s,frame :=
          {next.frame with remaining := selectKey carrier value arms otherwise ++ rest}}
    | .matchAdt site place arms otherwise =>
      match PV_STX2_Store.read carrier c.store w c.frame.activation place with
      | none => return gap (some site)
      | some value => match control.variant value with
        | none => return gap (some site)
        | some n => match selectVariant n arms otherwise with
          | none => return gap (some site)
          | some body => return running {next with frame :=
              {next.frame with remaining := body ++ rest}}
    | .binary site destination operator left right =>
      match operands carrier w c.frame.activation [left,right] c.store with
      | some ([l,r],s) => match control.binary operator l r with
        | none => return gap (some site)
        | some value => match locate carrier s w c.frame.activation destination with
          | none => return gap (some site)
          | some address => match writeAddress carrier s address (some value) with
            | none => return gap (some site)
            | some s' => return running {next with store := s'}
      | _ => return gap (some site)
    | .discriminant site destination source _ =>
      match PV_STX2_Store.read carrier c.store w c.frame.activation source with
      | none => return gap (some site)
      | some value => match control.variant value with
        | none => return gap (some site)
        | some n => match locate carrier c.store w c.frame.activation destination with
          | none => return gap (some site)
          | some address => match writeAddress carrier c.store address (some (.number n)) with
            | none => return gap (some site)
            | some s => return running {next with store := s}
    | .assertion site condition expected _ _ =>
      match operand carrier c.store w c.frame.activation condition with
      | none => return gap (some site)
      | some (value,s) => match carrier.truth value with
        | none => return gap (some site)
        | some b => return (if b = expected then running {next with store := s}
            else ⟨.fault .abort s,w,[]⟩) -- pinned panic=abort; UB abort retained

/-- Conditional on owner acceptance of the translator patch. Finite-prefix
execution does not count unused terminal fuel as transitions. -/
def advance {W E : Type} (carrier : Carrier W Data) (control : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data) :
    Nat → Prefix W E → Prefix W E
  | 0, p => p
  | n+1, p => match p.status with
    | .running c =>
      let q := step carrier control programs handler c p.world
      advance carrier control programs handler n ⟨q.status,q.world,p.events ++ q.events⟩
    | _ => p

#print axioms enter
#print axioms native
#print axioms adopt
#print axioms selectVariant
#print axioms selectKey
#print axioms step
#print axioms advance
end PV_STX2_SliceMachine
