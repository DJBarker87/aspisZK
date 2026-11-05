import NHS_NFWObligation
import NHS_PendingSource
import NGC_CheckpointBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_CheckpointPacket
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes3Namespaces
/-- Exact adopted preparation boundary plus actual initializer/loop records.
Both formerly OPEN NGC producer predicates are derived. Neither a writer
success nor an independent Fields/pending-output equality is a premise. -/
theorem source {F C H : Type} (configuration : DrvC_Installation.Configuration F C)
 (D : VTop_Stages.aspis_core.digest.Digest32 H)
 (semantic : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H)
 (input : Array VTop_Stages.aspis_core.field.wide_exact.WideExact 29#usize)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (parsed : ∃ parsed,(DrvC_Dictionary.ops (F3V_Install.configuration configuration)).op3 proof=ok (.Ok parsed))
 (scan : (DrvC_Dictionary.ops (F3V_Install.configuration configuration)).op4 proof=ok (.Ok ()))
 (preparation : (DrvC_Dictionary.ops (F3V_Install.configuration configuration)).op7
   D semantic proof hash none input=ok (.Ok p,g))
 (constructors : VTop_Stages.Ops) (reserveA : Bool)
 (reservation : NHS_PendingReservation.Reservation)
 (base : Port3_NativeQueryBody.Ops) (a after : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (raw rows : alloc.vec.Vec Port3_NativePendingBody.Row)
 (pending : verifier.BatchedWeights)
 (newA : (Port3_Constructor.installed constructors reserveA).op12 .S2=ok (.Ok a))
 (allocation : NHS_PendingReservation.heap reservation (Slice.len a.weights.deref)
   (Array.repeat 4#usize 0#u64)=ok (.Ok raw))
 (cuts : NHS_PendingTrace.Cuts a.weights.deref raw 0#usize rows)
 (accepted : Port3_NativeQueryBody.verifier.candidate.query_loop (NFS_QueryOps.installed base)
   proof p a g none geometry (verifier.BatchedWeights.mk rows 0#usize) 10#usize=ok (.Ok (after,pending))) :
 ∃ out : Slice aspis_core.field.QM31,
 ∃ domain : NGC_KNE_Caller.WriterDomain (toPrepared p)
   (toAccumulator {after with weights:=⟨out.val,out.property⟩}),
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 (∀ stored publicBytes : Slice U8,
   NGC_KNE_Writer.sourceProgram (toPrepared p)
     (toAccumulator {after with weights:=⟨out.val,out.property⟩}) domain stored publicBytes=
   CheckpointBytes5Writer.writer (toPrepared p)
     (toAccumulator {after with weights:=⟨out.val,out.property⟩}) stored publicBytes) ∧
 (∀ hp hu hc : CheckpointBytes5Effect.Digest,
   (NGC_KNE_Schedule.derivedSchedule (toPrepared p)
     (toAccumulator {after with weights:=⟨out.val,out.property⟩}) domain hp hu hc).length=116 ∧
   ∀ step∈NGC_KNE_Schedule.derivedSchedule (toPrepared p)
     (toAccumulator {after with weights:=⟨out.val,out.property⟩}) domain hp hu hc,
   step.len+step.size≤step.cap) := by
 have prepared := NHS_NFWObligation.source configuration D semantic proof hash input p g parsed scan preparation
 have initial := NHS_PendingSource.initial constructors reserveA reservation p a raw rows
   prepared.1 newA allocation cuts
 exact NGC_CheckpointBridge.derived_packet base proof p a after g geometry
   (verifier.BatchedWeights.mk rows 0#usize) pending initial.1 initial.2 prepared.1 accepted
#print axioms source
end AspisR1.NHS_CheckpointPacket
