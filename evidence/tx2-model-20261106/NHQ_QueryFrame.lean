import NHQ_Tx2CommonModel
import NFW_QueryResume
set_option autoImplicit false
noncomputable section
namespace NHQ_QueryFrame
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open NFW_QueryResume
theorem substitute (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (width : a.weights.val.length=64)
 (weights : NFS_NEV_WeightDomains.Canonical (NEV_AccumulateCarriers.fromAccumulator a).weights)
 (rhs : NBO_TailDomain.WideCanonical a.rhs) (power : NBF_PowerStep.Canonical a.power)
 (rho : NBF_PowerStep.Canonical p.rho) (start : a.next.val=10)
 (gamma : NFN_LPi_FieldValues.NE) (canonicalGamma : NFN_LPi_FieldValues.canonE gamma)
 (g : Array NFN_LPi_FieldValues.NE 29#usize)
 (powers : FIo_Native.weights.powers 29#usize gamma=ok g)
 (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat)
 (actual : Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error))
 (native_slot : actual = verifier.candidate.query_loop (NFS_QueryOps.installed base)
  proof p a (FIp_DotsAdapter.fromArray g) none geometry (pending a) 22#usize)
 (tail : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error →
   Result (core.result.Result Unit verifier.Error)) :
 (do let reply ← actual;tail reply) =
 (do let reply ← (NFG_QueryLoopDefs.run
   (NFS_QueryLoopRoot.child base proof p (FIp_DotsAdapter.fromArray g) geometry qPlace gPlace)
   22#usize 12 (.Ok (a,pending a)));tail reply) := by
 rw [native_slot,←NFW_QueryResume.tx2 base proof p a width weights rhs power rho start
  gamma canonicalGamma g powers geometry qPlace gPlace]
#print axioms substitute
end NHQ_QueryFrame
