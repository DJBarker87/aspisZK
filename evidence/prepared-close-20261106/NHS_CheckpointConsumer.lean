import NHS_PendingReservation
import NGC_KNE_Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_CheckpointConsumer
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes3Namespaces
/-- Actual initializer replies, SAME pending/weights, SAME query result and
SAME finish yield the local116-transition writer on its derived domain. -/
theorem source (constructors : VTop_Stages.Ops) (reserveA : Bool)
 (reservation : NHS_PendingReservation.Reservation)
 (base : Port3_NativeQueryBody.Ops) (proof publicBytes : Slice U8)
 (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry)
 (b pending : verifier.BatchedWeights) (prepared : NGC_PreparationBoundary.Fields p)
 (newA : (Port3_Constructor.installed constructors reserveA).op12 .S2=ok (.Ok a))
 (newB : NHS_PendingReservation.source reservation a.weights.deref=ok (.Ok b))
 (accepted : Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a g none geometry b 10#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 let written : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 ∃ domain : NGC_KNE_Caller.WriterDomain (toPrepared p) (toAccumulator written),
 NGC_KNE_Writer.sourceProgram (toPrepared p) (toAccumulator written) domain proof publicBytes=
   CheckpointBytes5Writer.writer (toPrepared p) (toAccumulator written) proof publicBytes ∧
 written.rhs=after.rhs ∧ written.power=after.power ∧ written.next=after.next := by
 have initial := NHS_PendingReservation.same_initial constructors reserveA reservation p a b prepared newA newB
 obtain ⟨out,flush,domain,frame⟩ := NGC_WriterDomain.from_query_loop
   base proof p a after g geometry b pending initial.1 initial.2 prepared accepted
 exact ⟨out,flush,domain,NGC_KNE_Writer.cohort_program_eq _ _ domain proof publicBytes,frame⟩
#print axioms source
end AspisR1.NHS_CheckpointConsumer
