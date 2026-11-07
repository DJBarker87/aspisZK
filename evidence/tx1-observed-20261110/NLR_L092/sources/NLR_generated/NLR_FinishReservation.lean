import NLR_ClaimsReservation
import NLR_FinishModelDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_FinishReservation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Infer the SAME VALUE-model reserve result, not an actual runtime reserve,
from the entered source finish success. No allocator fidelity is inferred. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
 (sem : r1_semantic.Verified H)
 (success : FinishModel.finish NJM_RoundJoin.R (IDa_Deployed.boundaries reservation)
  D pub pre before challenges none=ok (.Ok sem)) : reservation=.Ok () := by
 have installed : ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation)
  (IDa_Deployed.boundaries reservation)=IDa_Deployed.boundaries reservation := rfl
 have run := ClaimsUnrolledFinish.finish_claims (NP6_StdModel.calls reservation)
  NJM_RoundJoin.R (IDa_Deployed.boundaries reservation) D pub pre before challenges none sem
 rw [installed] at run
 have claims := (ClaimsUnrolledFinish.claims_value (NP6_StdModel.calls reservation) pre).trans (run success)
 exact NLR_ClaimsReservation.success reservation pre sem.claims claims
/-- The179 claims specialization is consequently the SAME successful source
finish. This is one source caller clause, not179's complete domain or native
parent ownership/allocator admission. -/
theorem constructor_clause (reservation : NP6_StdModel.Reservation) {H : Type}
 (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
 (sem : r1_semantic.Verified H)
 (success : FinishModel.finish NJM_RoundJoin.R (IDa_Deployed.boundaries reservation)
  D pub pre before challenges none=ok (.Ok sem)) :
 FinishModel.finish NJM_RoundJoin.R
  {IDa_Deployed.boundaries reservation with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
  D pub pre before challenges none=ok (.Ok sem) := by
 have same := source reservation D pub pre before challenges sem success
 subst reservation
 exact success
#print axioms source
#print axioms constructor_clause
set_option pp.proofs false
#print constructor_clause
end AspisR1.NLR_FinishReservation
end
