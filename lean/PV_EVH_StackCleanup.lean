import PV_EVH_StackZero
set_option autoImplicit false
namespace PV_EVH_StackCleanup
open Aeneas Aeneas.Std
open PV_EVH_Runtime (Outcome Fault)
open PV_EVH_HeapOwnership (Key)
open PV_EVH_StackZero (State Slot)
open PV_RJ4IDB (NativeEvent)

structure Run (A : Type) where
  outcome : Outcome A
  state : State
  events : List NativeEvent

abbrev Q (A : Type) := State → Run A

def lift {A : Type} (r : Result A) : Q A := fun w => ⟨.returned r,w,[]⟩

def bind {A B : Type} (m : Q A) (k : A → Q B) : Q B := fun w =>
  let r := m w
  match r.outcome with
  | .fault e => ⟨.fault e,r.state,r.events⟩
  | .exhausted => ⟨.exhausted,r.state,r.events⟩
  | .returned (.fail e) => ⟨.returned (.fail e),r.state,r.events⟩
  | .returned .div => ⟨.returned .div,r.state,r.events⟩
  | .returned (.ok a) =>
    let s := k a r.state
    ⟨s.outcome,s.state,r.events ++ s.events⟩

instance : Monad Q where
  pure a := lift (.ok a)
  bind := bind

def sameKey (key : Key) (slot : Slot) : Bool :=
  slot.key.identity == key.identity && slot.key.owner == key.owner

/-- Array drop looks up the original stack owner and checks the full source
array extent. It cannot redirect cleanup to an equal-valued allocation. -/
def drop64 (key : Key) : Q Unit := fun w =>
  match w.frame.live.find? (sameKey key) with
  | none => ⟨.fault (.invalidMemory key.identity),w,[]⟩
  | some slot =>
    if slot.initialized = 64 then
      ⟨.returned (.ok ()),PV_EVH_StackZero.drop slot w,PV_EVH_StackZero.emitted slot⟩
    else ⟨.fault (.invalidMemory key.identity),w,[]⟩

/-- Native Zeroizing<[u8;64]> cleanup after Rust's ordinary Result error.
Source/native stack admission remains a P obligation at the entry call site. -/
def fillScope {E B : Type} (key : Key) (fill : Q (core.result.Result Unit E))
    (consume : Q (core.result.Result B E)) : Q (core.result.Result B E) := do
  let r ← fill
  match r with
  | .Err e => do
    let _ ← drop64 key
    pure (.Err e)
  | .Ok _ => do
    let out ← consume
    let _ ← drop64 key
    pure out

theorem error_drop_full {E B : Type} (key : Key)
    (fill : Q (core.result.Result Unit E)) (consume : Q (core.result.Result B E))
    (w : State) (e : E) (slot : Slot)
    (hf : (fill w).outcome = .returned (.ok (.Err e)))
    (hs : (fill w).state.frame.live.find? (sameKey key) = some slot)
    (hn : slot.initialized = 64) :
    fillScope key fill consume w =
      ⟨.returned (.ok (.Err e)),PV_EVH_StackZero.drop slot (fill w).state,
        (fill w).events ++ PV_EVH_StackZero.emitted slot⟩ := by
  simp only [fillScope,Bind.bind,bind,hf,drop64,hs,hn,if_true,
    Pure.pure,lift,List.append_nil]

theorem error_zeroized {E B : Type} (key : Key)
    (fill : Q (core.result.Result Unit E)) (consume : Q (core.result.Result B E))
    (w : State) (e : E) (slot : Slot)
    (hf : (fill w).outcome = .returned (.ok (.Err e)))
    (hs : (fill w).state.frame.live.find? (sameKey key) = some slot)
    (hn : slot.initialized = 64) :
    PV_EVH_StackZero.Cleared slot (fillScope key fill consume w).state := by
  rw [error_drop_full key fill consume w e slot hf hs hn]
  exact PV_EVH_StackZero.dropped_cleared slot (fill w).state

theorem abort_preserves_prefix {E B : Type} (key : Key)
    (fill : Q (core.result.Result Unit E)) (consume : Q (core.result.Result B E))
    (w : State) (fault : Fault) (hf : (fill w).outcome = .fault fault) :
    fillScope key fill consume w = ⟨.fault fault,(fill w).state,(fill w).events⟩ := by
  simp only [fillScope,Bind.bind,bind,hf]

#print axioms error_drop_full
#print axioms error_zeroized
#print axioms abort_preserves_prefix
end PV_EVH_StackCleanup
