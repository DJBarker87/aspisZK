import NFW_QueryEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_QueryStart
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
/-- Installs the CLOSED NFS root on the exact powers result and initialized
caller states. The Prepared rho producer is the sole remaining primitive
canonicality premise, not the whole query-loop domain. -/
theorem tx1 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (gamma : NFN_LPi_FieldValues.NE) (canonicalGamma : NFN_LPi_FieldValues.canonE gamma)
 (g : Array NFN_LPi_FieldValues.NE 29#usize)
 (powers : FIo_Native.weights.powers 29#usize gamma=ok g)
 (rho : NBF_PowerStep.Canonical p.rho)
 (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat) :
 NFG_QueryLoopDefs.run
  (NFS_QueryLoopRoot.child base proof p (FIp_DotsAdapter.fromArray g) geometry qPlace gPlace)
  10#usize 10 (.Ok (NFW_QueryEntry.initial,NFW_QueryEntry.pending)) =
 verifier.candidate.query_loop (NFS_QueryOps.installed base) proof p NFW_QueryEntry.initial
  (FIp_DotsAdapter.fromArray g) none geometry NFW_QueryEntry.pending 10#usize := by
 exact NFS_QueryLoopRoot.tx1 base proof p NFW_QueryEntry.initial
  (FIp_DotsAdapter.fromArray g) geometry NFW_QueryEntry.pending qPlace gPlace
  (NFW_PowersDomain.query_domain gamma canonicalGamma g powers)
  (NFW_QueryEntry.domain p rho) rfl
#print axioms tx1
end AspisR1.NFW_QueryStart
