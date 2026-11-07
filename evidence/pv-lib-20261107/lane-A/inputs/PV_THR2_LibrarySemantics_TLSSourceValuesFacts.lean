import PV_FN_THREAD_f170_SourceValueConstructors
set_option autoImplicit false
noncomputable section
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_FN_THREAD_f170

/-- Constructor consequences of the documented returned-value clauses in
thread-24. All other answers remain unrestricted; no world, Store, region,
read-success or caller frame is asserted. The arbitrary type descriptors
retain the emitted generic instantiation. Source/body pins are unchanged from
session10/library-value-facets.json (ptr::as_ref, Option::ok_or, Try::branch). -/
def PV_THR2_LibrarySemantics_AsRef277Source {E : Type}
    (C : Carrier OWNER Data) (H : Backend E) : Prop :=
  ∀ e w v, let d := PV_W1_NativeLeaves.entry277 e e.arguments
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w
    r.answer = .returned (.ok v) →
    (∃ ty, v = (SourceTlsValue.optionNone ty).encode) ∨
      ∃ ty p original, e.arguments.head? = some original ∧
        C.dereference w original = some p ∧ v = (SourceTlsValue.optionSome ty p).encode

def PV_THR2_LibrarySemantics_OkOr278Source {E : Type} (H : Backend E) : Prop :=
  ∀ e w v, let d := PV_W1_NativeLeaves.entry278 e e.arguments
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w
    r.answer = .returned (.ok v) →
    (∀ ty, e.arguments.head? = some (SourceTlsValue.optionNone ty).encode →
      ∃ outTy, v = (SourceTlsValue.resultErr outTy).encode) ∧
    (∀ ty p, e.arguments.head? = some (SourceTlsValue.optionSome ty p).encode →
      ∃ outTy, v = (SourceTlsValue.resultOk outTy p).encode)

def PV_THR2_LibrarySemantics_Branch279Source {E : Type} (H : Backend E) : Prop :=
  ∀ e w v, let d := PV_W1_NativeLeaves.entry279 e e.arguments
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w
    r.answer = .returned (.ok v) →
    (∀ ty, e.arguments.head? = some (SourceTlsValue.resultErr ty).encode →
      ∃ outTy residualTy, v = (SourceTlsValue.controlBreak outTy residualTy).encode) ∧
    (∀ ty p, e.arguments.head? = some (SourceTlsValue.resultOk ty p).encode →
      ∃ outTy, v = (SourceTlsValue.controlContinue outTy p).encode)

namespace PV_FN_THREAD_f170
/-- Explicit lower fact inventory. These are the source-constructor portions
of the adopted exact-function semantics, never row Pre or frame premises. -/
structure DocumentedSourceFacts {E : Type} (C : Carrier OWNER Data) (H : Backend E) : Prop where
  asRef277Source : PV_THR2_LibrarySemantics_AsRef277Source C H
  okOr278Source : PV_THR2_LibrarySemantics_OkOr278Source H
  branch279Source : PV_THR2_LibrarySemantics_Branch279Source H

#print axioms DocumentedSourceFacts
end PV_FN_THREAD_f170
