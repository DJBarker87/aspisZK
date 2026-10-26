import R1Z.PDict_ReachClient1
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Absent-field irrelevance for the complete emitted `RealR1_client.prove_for_proof_accounts`. -/
theorem client_8 (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ (replace ops other) = @RealR1_client.prove_for_proof_accounts _ ops := by
  delta RealR1_client.prove_for_proof_accounts
  try simp only [client_6 ops other, client_7 ops other]
  all_goals rfl
#print axioms client_8
end R1Z.PDict_ReachErase
