import PV_BR_R1Z_PrivacyR1HeadlineDeployedReal

/- Original source module R1Z.PV_RJDec_V047; sha256 8f99805c4a763af0aa8cc4e74dab9255c676d33943bdd78c6ce3591478d27ad9. -/
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
