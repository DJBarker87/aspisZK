import NJC_ReaderResults
import NJC_ClosedCalls
set_option autoImplicit false
noncomputable section
namespace NJC_CutTypes
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Reviewed transcription of NJC_readers.rs::read_k, selected window shape.
Assertions: result.is_ok()==good; Ok kw(q)==expected; Err e==Checkpoint;
r.at==16; r.bytes.as_ptr()==bytes.as_ptr(); r.bytes.len()==16.
Source NJC_readers.rs.txt SHA256 c10e5e2e80cd18ec5c2b74baf73aa11e78b62376aa3e55d00b241760611ad05d. NO byte frame is inferred from the address. -/
def readerK (bytes : Array U8 16#usize)
 (reply : core.result.Result aspis_core.field.QM31 verifier.Error)
 (postCursor postLength beforeAddress afterAddress : Nat) : Prop :=
 reply=NJC_ReaderResults.naturalK bytes ∧ postCursor=16 ∧ postLength=16 ∧
 afterAddress=beforeAddress

/-- Reviewed NHV_native.rs::powers_check transcription. The harness's arbitrary
selected index spans all29 cells; no output success or callee result law is
asserted here. Source NHV_native.rs.txt SHA256 01644cdc29352595fb6850bb50103ce858a854d87a367ccd52a033679aed7483. Exact assertion:
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


/-- Reviewed one-iteration cut; source NJC_weight_step.rs.txt SHA256 4feba9ed9096fa8b64b9684e7c475f3111a07ca172d6edb77b7fbebe34188b79.
Assertions: result.is_ok()==good; Ok at==16 and words(values[j])==
(if j==i then expected else before[j]); Err Checkpoint and
words(values[j])==before[j]. j is arbitrary in0..64. No Vec allocation,
capacity, or caller producer association is asserted. -/
def weightStep (bytes : Array U8 16#usize)
 (before after : Array aspis_core.field.QM31 64#usize) (i : Fin 64)
 (reply : core.result.Result Usize verifier.Error) : Prop :=
 match NJC_ReaderResults.naturalK bytes with
 | .Err error => reply=.Err error ∧
   ∀ j : Fin 64, after.val[j.val]'(by rw [after.property];exact j.isLt)=
    before.val[j.val]'(by rw [before.property];exact j.isLt)
 | .Ok value => reply=.Ok 16#usize ∧
   ∀ j : Fin 64, after.val[j.val]'(by rw [after.property];exact j.isLt)=
    if j=i then value else before.val[j.val]'(by rw [before.property];exact j.isLt)

#print axioms weightStep

#print axioms readerK
#print axioms powers
#print axioms powers_array
end NJC_CutTypes
