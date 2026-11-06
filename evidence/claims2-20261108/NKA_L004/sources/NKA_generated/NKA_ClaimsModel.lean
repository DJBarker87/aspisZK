import NKA_Reservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_ClaimsModel
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent
open ClaimsUnrolledFinish

/-- Full owned-reference value after the actual reserve site. A returning
rejection is Allocation; native abort is covered separately by the cut. -/
def reserveResult (r : NP6_StdModel.Reservation) (value : Claims) : Result Status :=
 match r with
 | .Ok _ => ok (.Ok value)
 | .Err _ => ok (.Err .Allocation)

theorem rejected (e : NP6_StdModel.ReserveError) (pre : r1_wire.Prefix)
 (record : Record) (getter : sourceRecord pre 25#u8=ok (.Ok record)) :
 candidate_claims.claims (NKA_Reservation.external (.Err e)) pre=ok (.Err .Allocation) := by
 rw [claims_value]
 unfold claimsReference
 simp only [show (NKA_Reservation.external (.Err e)).validated pre 25#u8=ok (.Ok record) from getter]
 simp only [core.result.Result.Insts.CoreOpsTry.branch,zero,bind_tc_ok]
 rw [NKA_Reservation.rejected]
 simp [mapError,
  candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
  candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Reservation quantified, not assumed successful. The SAME parsed caller
supplies the record and makes all three decodes total before reordering them
past the allocation; no decoder success is a root premise. Native credit
still needs the unsafe P6 packet and its existing Allocator installation. -/
theorem parsed (r : NP6_StdModel.Reservation) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parser : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∃ value,
 NJT_ClaimsRef_Value.unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref
  (fromMainPrefix (PrefixAdapter.fromOld pre)))=ok (.Ok value) ∧
 candidate_claims.claims (NKA_Reservation.external r)
  (fromMainPrefix (PrefixAdapter.fromOld pre))=reserveResult r value := by
 obtain ⟨value,pure⟩:=NJT_AllocationLift.pure_success bytes pre parser
 refine ⟨value,pure,?_⟩
 cases r with
 | Ok unit =>
  cases unit
  change candidate_claims.claims NJT_ClaimsRef_Value.external _ = ok (.Ok value)
  rw [← NJT_ClaimsCohort.reference,pure]
 | Err e =>
  obtain ⟨record,getter,row,decoded⟩:=NJT_QClaimsCanonical.claims bytes pre parser
  have called : sourceRecord (fromMainPrefix (PrefixAdapter.fromOld pre)) 25#u8=
   ok (.Ok (⟨record.row,record.framed⟩ : Record)) := by
   unfold sourceRecord
   rw [NJT_AllocationLift.prefix_back,getter]
  exact rejected e _ _ called

#print axioms rejected
#print axioms parsed
#print parsed
end AspisR1.NKA_ClaimsModel
end
