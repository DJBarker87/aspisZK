import NJC_ReaderResults
import NJC_ClosedCalls
set_option autoImplicit false
noncomputable section
namespace NJC_CutTypes
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Reviewed transcription of NJC_readers.rs::read_k, selected window shape.
Assertions: result.is_ok()==good; Ok kw(q)==expected; Err e==Checkpoint;
r.at==16; r.bytes.as_ptr()==bytes.as_ptr(); r.bytes.len()==16.
Source/hash: NJC_SOURCE_PINS.json. NO byte frame is inferred from the address. -/
def readerK (bytes : Array U8 16#usize)
 (reply : core.result.Result aspis_core.field.QM31 verifier.Error)
 (postCursor postLength beforeAddress afterAddress : Nat) : Prop :=
 reply=NJC_ReaderResults.naturalK bytes ∧ postCursor=16 ∧ postLength=16 ∧
 afterAddress=beforeAddress

/-- Reviewed NHV_native.rs::powers_check transcription. The harness's arbitrary
selected index spans all29 cells; no output success or callee result law is
asserted here. Source/hash: NJC_INPUT_PINS.json. Exact assertion:
check(log.gamma==p.gamma&&g[selected]==expected&&log.calls==1). -/
def powers (gamma logged : aspis_core.field.wide_exact.WideExact)
 (reply output : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (calls : Nat) : Prop :=
 logged=gamma ∧ (∀ i : Fin 29,output.val[i.val]'(by rw [output.property];exact i.isLt)=
 reply.val[i.val]'(by rw [reply.property];exact i.isLt)) ∧ calls=1

/-- Whole-array assembly of exactly the arbitrary selected-cell assertion.
This discharges no callee law or producer domain. -/
theorem powers_array (gamma logged : aspis_core.field.wide_exact.WideExact)
 (reply output : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (calls : Nat) (cut : powers gamma logged reply output calls) : output=reply := by
 apply Subtype.ext
 apply List.ext_getElem
 · rw [output.property,reply.property]
 · intro i hi hj
   exact cut.2.1 ⟨i,by rw [output.property] at hi;exact hi⟩

#print axioms readerK
#print axioms powers
#print axioms powers_array
end NJC_CutTypes
