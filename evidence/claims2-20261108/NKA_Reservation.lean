import NJT_AllocationLift
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_Reservation
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent

def external (r : NP6_StdModel.Reservation) : External :=
 ClaimsUnrolledFinish.external (NP6_StdModel.calls r)

/-- Full reservation outcome at the named source call, with no success premise.
This is the model branch law; native heap interpretation is a separate cut. -/
theorem rejected (e : NP6_StdModel.ReserveError) (value : Row) :
 aspis_core.r0.heap.filled (external (.Err e))
  (Array.Insts.CoreMarkerCopy 29#usize aspis_core.field.QM31.Insts.CoreMarkerCopy)
  3#usize value = ok (.Err .Allocation) := by
 simp [aspis_core.r0.heap.filled, external, ClaimsUnrolledFinish.external,
  NP6_StdModel.calls, mapError,
  aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError,
  aspis_core.r0.heap.filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once,
  core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Same successful data interpretation as NJT; only the allocator result is
split here. It does not assert success for a quantified reservation. -/
theorem filled (value : Row) :
 aspis_core.r0.heap.filled (external (.Ok ()))
  (Array.Insts.CoreMarkerCopy 29#usize aspis_core.field.QM31.Insts.CoreMarkerCopy)
  3#usize value = ok (.Ok (NJT_ClaimsCohort.triple value)) := by
 exact NJT_ClaimsCohort.parent_filled value

#print axioms rejected
#print axioms filled
end AspisR1.NKA_Reservation
end
