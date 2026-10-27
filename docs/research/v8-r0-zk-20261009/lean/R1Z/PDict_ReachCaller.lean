import R1Z.PDict_ReachClient2
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachCaller
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op13_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op13 := other.op13 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op13 := other.op13 }
#print axioms op13_irrelevant

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op16_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op16 := other.op16 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op16 := other.op16 }
#print axioms op16_irrelevant

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op17_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op17 := other.op17 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op17 := other.op17 }
#print axioms op17_irrelevant

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op18_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op18 := other.op18 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op18 := other.op18 }
#print axioms op18_irrelevant

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op85_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op85 := other.op85 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op85 := other.op85 }
#print axioms op85_irrelevant

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op124_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op124 := other.op124 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op124 := other.op124 }
#print axioms op124_irrelevant

/-- Single-field source irrelevance, with all success/error/retry results retained. -/
theorem op238_irrelevant (ops other : ExternalFuns) :
    @RealR1_client.prove_for_proof_accounts _ { ops with op238 := other.op238 } =
      @RealR1_client.prove_for_proof_accounts _ ops := by
  exact PDict_ReachErase.client_8 ops { ops with op238 := other.op238 }
#print axioms op238_irrelevant
end R1Z.PDict_ReachCaller
