import R1Z.PrivacyR1HeadlineDeployedReal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_V047
open R0Z.ZkStatement
abbrev H := PhaseWireLog2Bin.honest PrivacyR1HeadlineDeployedReal.input
/-- Consume HeadlineFibre.fibre only after identifying the actual statement.
Neither the native handle nor its decoder equality is supplied by this rule. -/
theorem consume {CommitHandle : Type}
    (encoded actual : Statement PrivacyR1AcctBasis.K CommitHandle)
    (fibre : ∃ w : H.Instance, H.public w = encoded.1)
    (native_identification : actual = encoded) :
    ∃ w : H.Instance, H.public w = actual.1 := by
  rw [native_identification]
  exact fibre
#print axioms consume
end R1Z.PV_RJDec_V047
