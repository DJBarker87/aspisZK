import R1Z.PDict_FmtClient2
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ClientFormatterIndependent
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- Full actual proof-account source caller, with arbitrary entropy, hash and
account callbacks and every return/failure/divergence preserved. The removed
Debug callback is never executed; no native Formatter contract is assumed. -/
theorem client_erased (ops : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ (PDict_FormatterIndependent.erased ops) =
      @RealR1_client.prove_for_proof_accounts _ ops :=
  PDict_FmtErase.client_8 ops (PDict_FormatterIndependent.erased ops)
#print axioms client_erased
end R1Z.PDict_ClientFormatterIndependent
