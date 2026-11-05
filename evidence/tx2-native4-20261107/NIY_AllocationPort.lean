import NIY_WeightsPort
import NIY_QueryRead
import NIY_SectionBind
set_option autoImplicit false
noncomputable section
namespace NIY_AllocationPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (semantic_alpha : Array aspis_core.field.QM31 10#usize) (val6 : aspis_core.field.QM31) (val7 : aspis_core.field.QM31) (val8 : aspis_core.field.QM31) (val9 : aspis_core.field.QM31) (val10 : aspis_core.field.wide_exact.WideExact) (val11 : aspis_core.field.wide_exact.WideExact) (val12 : aspis_core.field.QM31) (r50 : verifier.Reader) :
 NIL_StatePort.reply (NIY_AfterPower.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 r50)=
 NIY_C_AfterPower.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (k val4) queries (array k semantic_alpha) (k val6) (k val7) (k val8) (k val9) (e val10) (e val11) (k val12) (reader r50) := by
 with_unfolding_all rw [NIY_AllocationCut.source,NIY_C_AllocationCut.source]
 unfold NIL_StatePort.reply
 with_unfolding_all rw [outer_bind]
 apply NIL_ResultCases.bind_congr
 intro n
 let zero : Cohort.K := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
 let allocated := NIL_FreshOps.filled reserved
   (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x)) n (unK zero)
 let convert := fun (reply : core.result.Result (alloc.vec.Vec Fresh.K) aspis_core.r0.Error)=>NIL_FreshOps.mapError
   (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (NIL_FreshOps.digest d)) reply ()
 let nextF := fun weights=>NIY_AllocationCut.suffix reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 weights r50
 let nextC := fun weights=>NIY_C_AllocationCut.suffix (CheckpointBytes4Ops.ops reserved) bytes (variant v) end1 i4 state a3 a4 (e val) (e val1) (e val2) (e val3) (k val4) queries (array k semantic_alpha) (k val6) (k val7) (k val8) (k val9) (e val10) (e val11) (k val12) weights (reader r50)
 change outer (NIL_Carriers.inner NIL_StatePort.pair)
   (do let reply ← allocated;let converted ← convert reply;NIL_TryTransport.fresh converted nextF)=
   (do let reply ← CheckpointBytes3Allocation.filled reserved n zero;NIL_TryTransport.cohort reply nextC)
 have assoc := NIY_QueryRead.assoc allocated convert (fun reply=>NIL_TryTransport.fresh reply nextF)
 rw [←assoc]
 have port := NIL_AllocationPort.source reserved (NIL_FreshOps.digest d) n (unK zero)
 have port' : outer (NIL_Carriers.inner (vec k)) (do let reply ← allocated;convert reply)=
   CheckpointBytes3Allocation.filled reserved n zero := by
  simpa only [k_reverse] using port
 apply NIY_SectionBind.forwardReply (vec k) (vec unK) NIL_StatePort.pair
   (vec_roundtrip k unK k_roundtrip) _ _ port'
 intro weights
 have h := NIY_WeightsPort.source reserved d bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries semantic_alpha val6 val7 val8 val9 val10 val11 val12 (vec unK weights) r50
 simpa only [NIL_StatePort.reply,nextF,nextC,vec_roundtrip unK k k_reverse] using h
#print axioms source
end NIY_AllocationPort
