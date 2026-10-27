import R1Z.PV_RunJoin_PublicAudit24
import R1Z.PV_RunJoin_CounterexampleAudit24
import R1Z.PrivacyR1HeadlineDeployedReal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FinalAudit24
/-- The endpoint's own input is canonical, rather than the raw native family. -/
theorem endpoint_input_is_canonical :
    PrivacyR1HeadlineDeployedReal.input =
      BuilderSource.prover (K := PrivacyR1AcctBasis.K) := rfl
#print axioms endpoint_input_is_canonical
end R1Z.PV_RunJoin_FinalAudit24
#print R1Z.PrivacyR1HeadlineDeployedReal.input
#print R1Z.PrivacyR1HeadlineDeployedReal.RustRealRefinement
#print R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#print axioms R1Z.PV_RunJoin_PaddingCounterexample24.identification_unsatisfiable
#print axioms R1Z.PV_RunJoin_PaddingCounterexample24.admitted_identification_unsatisfiable
