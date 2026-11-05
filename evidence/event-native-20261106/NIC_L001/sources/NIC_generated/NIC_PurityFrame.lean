import NIA_EventInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIC_PurityFrame
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1Stage2
open Port3_NativeQueryBody NFP_TraceTypes

/-- Structural interpretation of the certified alphabet on the SAME context.
Native unreachability certificates are external hybrid evidence, not inferred
from this theorem or from equality of returned values. -/
theorem context_frame {C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (base : Ops) (events : List Event) (context : C) (prior : SdkC_Source.Log) :
 ∃ out, (context,SdkC_Source.run hashv (NIA_EventInterpretation.eventsCode base events) prior)=
 (context,(out,prior)) ∧
 NHZ_DRIVER.Cuts hashv (NIA_EventInterpretation.eventsCode base events) out [] := by
 obtain ⟨out,t⟩ := NIA_EventInterpretation.no_reads_trace
   (NIA_EventInterpretation.events_no_reads base events) hashv
 refine ⟨out,?_,.leaf t⟩
 simpa only [List.append_nil] using congrArg (fun r => (context,r)) (NGQ_Cuts.run t prior)

/-- Install an effect-free event list before its actual returned continuation.
Failure/divergence are governed by Continuation, hence cannot acquire a suffix.
This is conditional model composition, never a physical TX1 producer. -/
theorem compose {A : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (base : Ops) (events : List Event) (out : Result Unit)
 (head : NHZ_DRIVER.Cuts hashv (NIA_EventInterpretation.eventsCode base events) out [])
 (k : Unit → Code A) (final : Result A) (suffix : SdkC_Source.Log)
 (tail : NHK_TraceBind.Continuation hashv out k final suffix) :
 NHZ_DRIVER.Cuts hashv
 (CheckpointBytes5Effect.bind (NIA_EventInterpretation.eventsCode base events) k) final suffix := by
 have t := NHK_TraceBind.append (NHZ_DRIVER.trace head) k final suffix tail
 exact .leaf (by simpa only [List.nil_append] using t)

#print axioms context_frame
#print axioms compose
end AspisR1.NIC_PurityFrame
