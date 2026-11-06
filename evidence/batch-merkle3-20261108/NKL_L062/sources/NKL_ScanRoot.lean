import NKL_ScanSequence
set_option autoImplicit false
noncomputable section
namespace NKL_ScanRoot
open Aeneas Aeneas.Std Result AspisR1 NKL_Checks NKL_ScanAtoms NKL_NativeGuard NKL_ScanSequence

theorem all_source (xs:List Check) (domains:∀ c∈xs,NKL_ScanDomains.Domain c) :
 xs.all nativeGuard=xs.all test := by
 induction xs with
 | nil=>rfl
 | cons c cs ih=>
   rw [List.all_cons,List.all_cons,NKL_NativeGuard.source c (domains c (by simp))]
   rw [ih (by intro d member;exact domains d (by simp [member]))]

/-- The only proof premise is the reviewed source-ordered native-cut
transcription, instantiated with CLOSED child bodies. The input carrier itself
establishes every domain; there is no Ops, child-success or endpoint premise. -/
theorem deployed (proof:Array U8 57607#usize) (out:Reply) (events:List Check) (after:Bytes)
 (native:Invoke (checks proof.to_slice) out events proof.val after) :
 ok out=NJS_Extract.verifier.candidate.canonical_scan
  AspisR1M31Parser.field.M31.from_le_bytes NKL_CanonicalInstallation.childK
  NKL_CanonicalInstallation.childE NKL_CanonicalInstallation.childCV proof.to_slice ∧
 after=proof.val ∧ ∃ suffix,events++suffix=checks proof.to_slice := by
 have whole:=NKL_ScanSequence.exact native
 have result:=NKL_ScanSequence.result (checks proof.to_slice)
 rw [all_source _ (NKL_ScanDomains.source proof.to_slice proof.property),
  NKL_ScanModel.value proof.to_slice proof.property] at result
 constructor
 · rw [NKL_ScanModel.source proof.to_slice proof.property,whole.1,result]
 · exact ⟨whole.2.2,by rw [whole.2.1];exact NKL_ScanSequence.trace_prefix _⟩

theorem adopted (proof:Array U8 57607#usize) (out:Reply) (events:List Check) (after:Bytes)
 (native:Invoke (checks proof.to_slice) out events proof.val after) :
 ok out=(do let valid←MultiproofParserRef.parser_reference.scan proof.to_slice
            ok (NKB_CanonicalOpening.reply valid)) := by
 rw [(deployed proof out events after native).1,NKL_ScanModel.adopted proof.to_slice proof.property]

theorem no_later_event (proof:Array U8 57607#usize) (events:List Check) (after:Bytes)
 (native:Invoke (checks proof.to_slice) (.Err .Parse) events proof.val after) :
 ∃ before bad suffix,checks proof.to_slice=before++bad::suffix ∧
 events=before++[bad] ∧ before.all nativeGuard=true ∧ nativeGuard bad=false := by
 have whole:=NKL_ScanSequence.exact native
 obtain ⟨before,bad,suffix,order,trace,prior,err⟩:=
  NKL_ScanSequence.rejection_trace (checks proof.to_slice) whole.1.symm
 exact ⟨before,bad,suffix,order,whole.2.1.trans trace,prior,err⟩

theorem success_events (proof:Array U8 57607#usize) (events:List Check) (after:Bytes)
 (native:Invoke (checks proof.to_slice) (.Ok ()) events proof.val after) :
 events=checks proof.to_slice := by
 have whole:=NKL_ScanSequence.exact native
 exact whole.2.1.trans (NKL_ScanSequence.success_trace _ whole.1.symm)

set_option pp.proofs false
#print deployed
#print adopted
#print no_later_event
#print axioms all_source
#print axioms deployed
#print axioms adopted
#print axioms no_later_event
#print axioms success_events
end NKL_ScanRoot
end
