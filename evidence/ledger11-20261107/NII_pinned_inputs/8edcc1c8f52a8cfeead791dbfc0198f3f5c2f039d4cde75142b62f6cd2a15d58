import NGC_WriterDomain
import NGC_DigestBridge
import NGC_KNE_Final
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_CheckpointBridge
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes3Namespaces CheckpointBytes5Writer
/-- All 116 transitions and all chronological digest replies agree with the
adopted writer on the derived SAME prestate. This is the model side of the
hybrid packet; native association is the controlled source-fission packet. -/
theorem derived_packet (base : Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry)
 (b pending : verifier.BatchedWeights) (domain : NFS_QueryInvariant.Domain p 0 10 a b)
 (start : a.next.val=0) (prepared : NGC_PreparationBoundary.Fields p)
 (accepted : Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 10#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 ∃ writerDomain : NGC_KNE_Caller.WriterDomain (toPrepared p)
  (toAccumulator {after with weights:=⟨out.val,out.property⟩}),
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 (∀ stored publicBytes : Slice U8,
  NGC_KNE_Writer.sourceProgram (toPrepared p)
   (toAccumulator {after with weights:=⟨out.val,out.property⟩}) writerDomain stored publicBytes=
  writer (toPrepared p) (toAccumulator {after with weights:=⟨out.val,out.property⟩}) stored publicBytes) ∧
 (∀ hp hu hc : CheckpointBytes5Effect.Digest,
  (NGC_KNE_Schedule.derivedSchedule (toPrepared p)
   (toAccumulator {after with weights:=⟨out.val,out.property⟩}) writerDomain hp hu hc).length=116 ∧
  ∀ step ∈ NGC_KNE_Schedule.derivedSchedule (toPrepared p)
   (toAccumulator {after with weights:=⟨out.val,out.property⟩}) writerDomain hp hu hc,
   step.len+step.size≤step.cap) := by
 obtain ⟨out,run,writerDomain,_⟩ := NGC_WriterDomain.from_query_loop base proof p a after g geometry b pending domain start prepared accepted
 exact ⟨out,writerDomain,run,
  fun stored publicBytes=>NGC_KNE_Writer.cohort_program_eq _ _ writerDomain stored publicBytes,
  fun hp hu hc=>NGC_KNE_Final.schedule_facts _ _ writerDomain hp hu hc⟩
#print axioms derived_packet
end AspisR1.NGC_CheckpointBridge
end
