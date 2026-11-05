import NIF_FieldsTotal
import NIC_PurityFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_FieldsEffect
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1Stage2
open Port3_NativeQueryBody NFP_TraceTypes OraclePortCompactDraft MultiproofConeCanonical
/-- Successful effect interpretation is DERIVED from canonical caller bytes;
the native certificate is K001/K002, not inferred from this model theorem. -/
theorem trace (hashv : SdkC_Source.Parts→Result SdkC_Source.Digest)
 (base : Ops) (q : Slice U8) (size : q.val.length=832)
 (checked : canonical (slice (bytesOf q.val) 672 128)) :
 NGQ_Cuts.Trace hashv (NIA_EventInterpretation.eventCode base (.fields q)) (.ok ()) [] := by
 obtain ⟨values,returned⟩:=NIF_FieldsTotal.fields base q size checked
 exact .stepOk _ _ values returned _ _ (.done ())

theorem same_context {C : Type} (hashv : SdkC_Source.Parts→Result SdkC_Source.Digest)
 (base : Ops) (q : Slice U8) (size : q.val.length=832)
 (checked : canonical (slice (bytesOf q.val) 672 128))
 (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (NIA_EventInterpretation.eventCode base (.fields q)) prior)=
 (context,(.ok (),prior)) := by
 have h:=NGQ_Cuts.run (trace hashv base q size checked) prior
 simpa only [List.append_nil] using congrArg (fun x=>(context,x)) h
#print axioms trace
#print axioms same_context
end AspisR1.NIF_FieldsEffect
