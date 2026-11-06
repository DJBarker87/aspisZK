import RPz7_NP6_StdModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_ClaimsReservation
open Aeneas Aeneas.Std Result
/-- VALUE model only: a returning Claims success entails the reserve outcome
used by THAT model. This does not prove actual allocator fidelity/ownership. -/
theorem success (reservation : NP6_StdModel.Reservation) (pre : ClaimsUnrolledFinish.MainPrefix)
 (out : ClaimsUnrolledFinish.MainClaims)
 (returned : ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation) pre=ok (.Ok out)) :
 reservation=.Ok () := by
 cases reservation with
 | Ok u => cases u;rfl
 | Err err =>
  rw [ClaimsUnrolledFinish.claims_value] at returned
  unfold ClaimsUnrolledFinish.reference AspisR1ClaimsUnrolledParent.claimsReference at returned
  simp only [ClaimsUnrolledFinish.external] at returned
  generalize hv : ClaimsUnrolledFinish.sourceRecord (ClaimsUnrolledFinish.fromMainPrefix pre) 25#u8 = record at returned
  cases record with
  | fail e => cases returned
  | div => cases returned
  | ok r =>
   cases r with
   | Err e => cases returned
   | Ok vr =>
    simp only [NP6_StdModel.calls,AspisR1ClaimsUnrolledParent.zero,
     AspisR1ClaimsUnrolledParent.aspis_core.r0.heap.filled,
     AspisR1ClaimsUnrolledParent.mapError,bind_tc_ok,
     core.result.Result.Insts.CoreOpsTry.branch,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame.from,ClaimsUnrolledFinish.toMainStatus,
     ClaimsUnrolledFinish.toMainError] at returned
    cases returned
#print axioms success
end AspisR1.NLR_ClaimsReservation
end
