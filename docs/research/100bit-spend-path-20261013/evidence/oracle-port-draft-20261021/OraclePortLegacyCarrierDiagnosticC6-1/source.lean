import OraclePortConsumer
import OraclePortReachedRunC6

/-! Deliberate type check of the direct inherited consumer application.
This diagnostic is archived as text after recording the rejected join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortLegacyCarrierDiagnosticC6
variable (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
#check OraclePortConsumer.clean_of_checks D OraclePortReachedRunC6.decision P
end AspisR1.OraclePortLegacyCarrierDiagnosticC6
end
