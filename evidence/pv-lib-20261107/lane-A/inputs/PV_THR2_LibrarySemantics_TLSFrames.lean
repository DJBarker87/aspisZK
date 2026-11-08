import PV_FN_W4_NativeFootprint
import PV_FN_THREAD_f170_NativeCalls
import PV_FN_W4_ReplaceEffects
set_option autoImplicit false
noncomputable section
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_FN_W4_NativeFootprint

/- Exact memory facets under thread-16. Source, toolchain and emitted-type pins
are recorded in evidence/pv-w4-20261108/session7-library-frames.json.
These are named semantic Prop parameters, never axioms or caller frame premises.

277: core::ptr::const_ptr::as_ref; no stores, including before a validity fault.
278: Option<&bool>::ok_or(AccessError); by-value match, no droppable payload.
279: Result<&bool,AccessError>::branch; by-value match only.
280: Result<Infallible,AccessError>::from_residual into the same error type;
     the From<AccessError> conversion is the blanket identity conversion.
These facts specify only the memory facet needed here. No successful return,
valid pointer, payload value, event or backend-world equality is inferred.
Rust docs: primitive.pointer.html#method.as_ref,
option/enum.Option.html#method.ok_or, result/enum.Result.html;
core source: ptr/const_ptr.rs, option.rs, result.rs, convert/mod.rs.
-/

def PV_THR2_LibrarySemantics_AsRef277 (C : Carrier OWNER Data) (D : Effects) : Prop :=
  ∀ e w args, let d := PV_W1_NativeLeaves.entry277 e args
    Confined C d w (D d w) (fun _ => False)
def PV_THR2_LibrarySemantics_OkOr278 (C : Carrier OWNER Data) (D : Effects) : Prop :=
  ∀ e w args, let d := PV_W1_NativeLeaves.entry278 e args
    Confined C d w (D d w) (fun _ => False)
def PV_THR2_LibrarySemantics_Branch279 (C : Carrier OWNER Data) (D : Effects) : Prop :=
  ∀ e w args, let d := PV_W1_NativeLeaves.entry279 e args
    Confined C d w (D d w) (fun _ => False)
def PV_THR2_LibrarySemantics_FromResidual280 (C : Carrier OWNER Data) (D : Effects) : Prop :=
  ∀ e w args, let d := PV_W1_NativeLeaves.entry280 e args
    Confined C d w (D d w) (fun _ => False)

/-- Memory facet for the exact emitted Cell<bool>::replace leaf289. It writes
only the bool cell addressed by its first argument, even though generic
Writable can follow the cell's type-erased representation further. The source
argument is a typed shared Cell reference and a literal bool, not a supplied
intermediate read. This frame facet asserts neither validity nor a successful
read/return. Source: core/src/cell.rs Cell::replace -> mem::replace; docs:
https://doc.rust-lang.org/std/cell/struct.Cell.html#method.replace .
Failure, divergence and pending remain arbitrary full answers. -/
def PV_THR2_LibrarySemantics_CellBoolReplace289 (C : Carrier OWNER Data)
    (D : Effects) : Prop :=
  ∀ e w p (v : Bool),
    let d := PV_FN_THREAD_f289.entry e
      [PV_STX2_TypedReferences.reference p .null,.boolean v]
    Confined C d w (D d w) (fun q => q = {p with fields := []})

namespace PV_FN_THREAD_f170_NativeFrames
open PV_W1_OwnerNativeFrame

/-- Strengthens CLOSED277; every permitted implementation delta remains a
parameter and W1's original contract is instantiated by name. -/
theorem f277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_AsRef277 C D)
    (e : Entry) (H : Backend E) (w : OWNER) (args : List Data) (es : List E)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    let d := PV_W1_NativeLeaves.entry277 e args
    PV_W1_NativeLeaves.Post277 C e H w args es (D d w) ∧
    (∀ q, q.activation ≠ e.store.nextActivation →
      q ≠ (⟨e.caller,e.destination,[]⟩ : Address) →
      (statusStore (deliver C (PV_W1_ArgumentEffects.afterEffects C d w (D d w))
        (PV_THR2_OwnUniformResourceHandler.lift H
          (.child d.callee d.store.nextActivation d.arguments) w) es).current.status).cells q =
        e.store.cells q) := by
  refine ⟨PV_W1_NativeLeaves.f277 C e H w args es _ pre,?_⟩
  intro q old notReturn
  exact deliverFrame C _ H w es _ (fun _ => False) (library e w args) q
    (fun h => h) old notReturn
#print axioms f277

/-- Strengthens CLOSED278; every permitted implementation delta remains a
parameter and W1's original contract is instantiated by name. -/
theorem f278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_OkOr278 C D)
    (e : Entry) (H : Backend E) (w : OWNER) (args : List Data) (es : List E)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    let d := PV_W1_NativeLeaves.entry278 e args
    PV_W1_NativeLeaves.Post278 C e H w args es (D d w) ∧
    (∀ q, q.activation ≠ e.store.nextActivation →
      q ≠ (⟨e.caller,e.destination,[]⟩ : Address) →
      (statusStore (deliver C (PV_W1_ArgumentEffects.afterEffects C d w (D d w))
        (PV_THR2_OwnUniformResourceHandler.lift H
          (.child d.callee d.store.nextActivation d.arguments) w) es).current.status).cells q =
        e.store.cells q) := by
  refine ⟨PV_W1_NativeLeaves.f278 C e H w args es _ pre,?_⟩
  intro q old notReturn
  exact deliverFrame C _ H w es _ (fun _ => False) (library e w args) q
    (fun h => h) old notReturn
#print axioms f278

/-- Strengthens CLOSED279; every permitted implementation delta remains a
parameter and W1's original contract is instantiated by name. -/
theorem f279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_Branch279 C D)
    (e : Entry) (H : Backend E) (w : OWNER) (args : List Data) (es : List E)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    let d := PV_W1_NativeLeaves.entry279 e args
    PV_W1_NativeLeaves.Post279 C e H w args es (D d w) ∧
    (∀ q, q.activation ≠ e.store.nextActivation →
      q ≠ (⟨e.caller,e.destination,[]⟩ : Address) →
      (statusStore (deliver C (PV_W1_ArgumentEffects.afterEffects C d w (D d w))
        (PV_THR2_OwnUniformResourceHandler.lift H
          (.child d.callee d.store.nextActivation d.arguments) w) es).current.status).cells q =
        e.store.cells q) := by
  refine ⟨PV_W1_NativeLeaves.f279 C e H w args es _ pre,?_⟩
  intro q old notReturn
  exact deliverFrame C _ H w es _ (fun _ => False) (library e w args) q
    (fun h => h) old notReturn
#print axioms f279

/-- Strengthens CLOSED280; every permitted implementation delta remains a
parameter and W1's original contract is instantiated by name. -/
theorem f280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_FromResidual280 C D)
    (e : Entry) (H : Backend E) (w : OWNER) (args : List Data) (es : List E)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    let d := PV_W1_NativeLeaves.entry280 e args
    PV_W1_NativeLeaves.Post280 C e H w args es (D d w) ∧
    (∀ q, q.activation ≠ e.store.nextActivation →
      q ≠ (⟨e.caller,e.destination,[]⟩ : Address) →
      (statusStore (deliver C (PV_W1_ArgumentEffects.afterEffects C d w (D d w))
        (PV_THR2_OwnUniformResourceHandler.lift H
          (.child d.callee d.store.nextActivation d.arguments) w) es).current.status).cells q =
        e.store.cells q) := by
  refine ⟨PV_W1_NativeLeaves.f280 C e H w args es _ pre,?_⟩
  intro q old notReturn
  exact deliverFrame C _ H w es _ (fun _ => False) (library e w args) q
    (fun h => h) old notReturn
#print axioms f280
end PV_FN_THREAD_f170_NativeFrames
