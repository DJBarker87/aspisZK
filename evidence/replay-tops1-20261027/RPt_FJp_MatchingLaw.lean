import RPt_FJp_MatchingAt
import RPt_FJp_GlobalOwners
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_MatchingLaw
/-- Checked implementation instance of the collision-aware matching join. -/
theorem value {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    FJp_GlobalOwners.Matching (FIp_Install.configuration err seed r) B := by
  intro s H e i p q data atPrepared prior
  exact FJp_MatchingAt.value err seed r B s H e i p q data atPrepared prior
#print axioms value
end AspisR1.FJp_MatchingLaw
end
