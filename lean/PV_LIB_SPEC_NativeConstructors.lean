import PV_LIB_SPEC_NativeBoolArc
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeConstructors
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
/-- Rust 1.94.1 atomic.rs530-531: AtomicBool stores UnsafeCell<u8>,
not UnsafeCell<bool>. N95807 makes AtomicBool opaque; this is the named
source-value interpretation, not an extracted field declaration. -/
def boolCell : Data := .object [("Adt",.array [
  .object [("id",.object [("Adt",.number 116)]),("generics",.object [
    ("regions",.array []),("types",.array [.object [("Literal",.object [("UInt",.atom "U8")])]]),
    ("const_generics",.array []),("trait_refs",.array [])])],.null,.null])]
def atomicBool (v : Bool) : Data :=
  PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.atomicBool
    [PV_THR2_KeyValues.pack boolCell [.number (if v then 1 else 0)]]
/-- Exact opaque source constructors used before callback allocation.
MaybeDangling::new wraps the moved F; UnsafeCell::new wraps its argument.
No chosen reply image or Store transformer appears in this graph. -/
def value (fn : Data) (args : List Data) : Option Data :=
  match PV_THR2_OffPath.functionId fn,args with
  | some 123,[.boolean b] => some (atomicBool b)
  | some 455,[v] => some (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.unsafeCell [v])
  | some 456,[v] => some (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.maybeDangling [v])
  | _,_ => none

def selected (request : PV_STX2_Native.Request Data) : Bool :=
  match request with
  | .child fn _ _ => match PV_THR2_OffPath.functionId fn with
    | some 123 | some 455 | some 456 => true
    | _ => false
  | _ => false

/-- Full failure/pending/fault arms are retained. On returned success,
malformed arguments expose None; no arbitrary successful value is substituted.
Constructors frame the entire world on EVERY answer. -/
def reply (request : PV_STX2_Native.Request Data) (w : OWNER)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match request with
  | .child fn _ args =>
    match r.answer with
    | .returned (.ok _) => (value fn args).map (fun v => ⟨.returned (.ok v),w,r.events⟩)
    | _ => some ⟨r.answer,w,r.events⟩
  | _ => none

theorem returned (fn : Data) (a : Nat) (args : List Data) (w : OWNER)
    (ignored : Data) (after : OWNER) (events : List Event) :
    reply (.child fn a args) w ⟨.returned (.ok ignored),after,events⟩ =
      (value fn args).map (fun v => ⟨.returned (.ok v),w,events⟩) := rfl

theorem other (fn : Data) (a : Nat) (args : List Data) (w : OWNER)
    (r : Reply OWNER Event Data)
    (notSuccess : ∀ v, r.answer ≠ .returned (.ok v)) :
    reply (.child fn a args) w r = some ⟨r.answer,w,r.events⟩ := by
  rcases r with ⟨answer,after,events⟩
  cases answer with
  | pending => rfl
  | fault f => rfl
  | returned out => cases out with
    | ok v => exact False.elim (notSuccess v rfl)
    | fail e => rfl
    | div => rfl

theorem framed (request : PV_STX2_Native.Request Data) (w : OWNER)
    (before after : Reply OWNER Event Data) (result : reply request w before = some after) :
    after.world = w := by
  cases request with
  | child fn a args =>
    cases h : before.answer with
    | pending => simp only [reply,h] at result; cases result; rfl
    | fault f => simp only [reply,h] at result; cases result; rfl
    | returned out => cases out with
      | fail e => simp only [reply,h] at result; cases result; rfl
      | div => simp only [reply,h] at result; cases result; rfl
      | ok v =>
        simp only [reply,h] at result
        cases hv : value fn args with
        | none => rw [hv] at result; cases result
        | some v => rw [hv] at result; cases result; rfl
  | drop f v => cases result
  | copy s d n => cases result

/-- Canonical initial source AtomicBool now agrees with the repaired scope
image for EVERY native Thread word. The old decoder rejects this same value. -/
theorem initial_scope (w : OWNER) (word : PV_OWN2_Codec.Pointer) :
    PV_LIB_SPEC_NativeBoolArc.image PV_LIB_SPEC_ScopeAllocationGap.C
      PV_LIB_SPEC_ScopeAllocationGap.K w .scope
      (PV_LIB_SPEC_ScopeAllocationGap.atomic 1) (PV_LIB_SPEC_ScopeAllocationGap.atomic 1)
      (PV_THR2_ScopeData.value (PV_LIB_SPEC_ScopeAllocationGap.atomic 0)
        (PV_THR2_OwnInitPointerCodec.encode word) (atomicBool false)) =
      some (PV_LIB_SPEC_AllocationImages.scope word.val) :=
  PV_LIB_SPEC_NativeBoolArc.scope_image_u8 w word _ _

#print axioms boolCell
#print axioms atomicBool
#print axioms value
#print axioms selected
#print axioms reply
#print axioms returned
#print axioms other
#print axioms framed
#print axioms initial_scope
end PV_LIB_SPEC_NativeConstructors
