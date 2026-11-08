import PV_LIB_SPEC_AtomicBindings13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsBindings13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
local instance : DecidableEq Data := Classical.decEq _
local instance : DecidableEq Address := Classical.decEq _

/-- Finite initialized ACTIVE TLS backing, distinct from current-Thread TLS.
This is data; correspondence is tested at the actual source/native request.
It does not certify uninitialized/destroyed TLS or the dropping-key branch. -/
structure Slot where
  source : Address
  physical : Nat

def read (slot : Slot) (p : Parameters) (c : Config) (w : OWNER) : Option Bool := do
  let .boolean b ← readAddress (runtime p).carrier c.store slot.source | none
  if w.world.memory slot.physical = some (if b then 1 else 0) then some b else none

def selected (request : PV_STX2_Native.Request Data) : Bool :=
  match PV_THR2_FnOnceDispatch.request request with
  | .child fn _ _ => decide (fn = (PV_THR2_KeyValues.castToken false).2 ∨
      fn = PV_THR2_F2Call.descriptors.2)
  | _ => false

/-- The no-drop TLS getter is the exact emitted FnDef469 token, derived from
F169.node11. Initialization arguments other than source None are unsupported.
Cell::get18 then reads the actual source pointee. No future TLS success or
opaque marker is supplied. A false ACTIVE cell admits entry into workers. -/
def value (slot : Slot) (p : Parameters) (c : Config) (w : OWNER)
    (request : PV_STX2_Native.Request Data) : Option Data := do
  match PV_THR2_FnOnceDispatch.request request with
  | .child fn _ args =>
    if fn = (PV_THR2_KeyValues.castToken false).2 then
      match args with
      | [init] =>
        if (runtime p).control.variant init = some 0 then do
          let _ ← read slot p c w
          pure (PV_STX2_TypedReferences.reference slot.source .null)
        else none
      | _ => none
    else if fn = PV_THR2_F2Call.descriptors.2 then
      match args with
      | [reference] => do
        let source ← (runtime p).carrier.dereference w reference
        if source=slot.source then do
          let b ← read slot p c w
          pure (.boolean b)
        else none
      | _ => none
    else none
  | _ => none

def reply (slot : Slot) (p : Parameters) (c : Config) (w : OWNER)
    (request : PV_STX2_Native.Request Data) (r : Reply OWNER Event Data) :
    Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let v ← value slot p c w request
    pure ⟨.returned (.ok v),w,r.events⟩
  | _ => some {r with world := w}

/-- TLS/Cell reads frame the entire world on EVERY answer. Events and all
non-success statuses remain the backend's full answer. -/
theorem world (slot : Slot) (p : Parameters) (c : Config) (w : OWNER)
    (request : PV_STX2_Native.Request Data) (r out : Reply OWNER Event Data)
    (result : reply slot p c w request r = some out) :
    out.world = w ∧ out.events = r.events := by
  unfold reply at result
  split at result
  · cases h : value slot p c w request with
    | none => simp only [h,Option.bind_none] at result; cases result
    | some v =>
      rw [h] at result
      change some _ = some out at result
      cases result; exact ⟨rfl,rfl⟩
  · cases result; exact ⟨rfl,rfl⟩

#print axioms Slot
#print axioms read
#print axioms selected
#print axioms value
#print axioms reply
#print axioms world
end PV_LIB_SPEC_TlsBindings13
