import NNG_StateCalls094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_QuerySource094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094 NNG_StateCalls094
/-- Exact CLOSED constructor source with both reservation replies. -/
theorem accumulator (env : RSL.Env) :
 accNew env=NMP_ResultTransport.outer (fromReply (fromT15 ∘ LIBC_VStateCarriers.fromAcc))
  (AspisR1.Port3_Constructor.extracted (AspisR1.Port3_Constructor.leaves env.reservation) .S2) := by
 unfold accNew
 rw [LIBC_AccNew.source]
#print axioms accumulator
/-- The same original proof and every current state argument, with the
CLOSED one-step/induction source theorem; no native cut image. -/
theorem query (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (finish : Usize)
 (domain : LIBC_QueryLoop.Domain (LIB_Carriers.bytes proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,finish.val)) :
 queryLoop env proof p a g geo pending finish=
 NMP_ResultTransport.outer (fromReply (fun r=>(fromT15 (LIBC_VStateCarriers.fromAcc r.1),fromT13 r.2)))
 (AspisR1.Port3_QueryInstall.result
  (AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop LIBC_QueryOps.ops proof
   (LIBC_QueryLoop.nativeP (LIB_Carriers.bytes proof,toT12 p,toT15 a,arr toT3 g,toT14 geo,toT13 pending,finish.val))
   (LIBC_VStateCarriers.toAcc (toT15 a))
   (AspisR1.NFW_PreparedPort.map AspisR1.NFW_PreparedPort.e (arr toT3 g)) none
   (toT14 geo) (toT13 pending) (LIBC_Usize.raw finish.val))) := by
 unfold queryLoop
 rw [LIBC_QueryLoop.source _ env domain,LIBC_Bytes.from_native]
#print axioms query
end AspisR1.NNG_QuerySource094
