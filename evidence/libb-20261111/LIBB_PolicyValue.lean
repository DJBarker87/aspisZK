import NND_PolicyCarrier
import LIBB_ResultTotal
import NHY_PolicyModel
set_option autoImplicit false
noncomputable section
namespace LIBB_PolicyValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier LIBB_ResultTotal

def unpolicy (p : RSL.VerifierPolicy) : aspis_statement.pool_v1.format.VerifierPolicyV1 :=
 ⟨unbyte p.flags,unkey p.registry_program,unkey p.registry_authority,unkey p.policy_binding⟩

theorem back (p : aspis_statement.pool_v1.format.VerifierPolicyV1) : unpolicy (policy p) = p := by
 cases p
 simp [unpolicy,policy]

theorem forth (p : RSL.VerifierPolicy) : policy (unpolicy p) = p := by
 cases p
 simp [unpolicy,policy]

theorem total (p : aspis_statement.pool_v1.format.VerifierPolicyV1) : Total (NHY_PolicyModel.policy p) := by
 rw [NHY_PolicyModel.value]
 exact pure _

def isOk {A E : Type} : core.result.Result A E → Bool
 | .Ok _ => true | .Err _ => false

def validate (p : RSL.VerifierPolicy) : Bool :=
 isOk (value (NHY_PolicyModel.policy (unpolicy p)) (total _))

theorem native (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :
 LIBB_ResultTotal.mapOuter isOk (NHY_PolicyModel.policy p) = ok (validate (policy p)) := by
 unfold validate
 simp only [back]
 conv_lhs => rw [equation _ (total p)]
 rfl

#print axioms back
#print axioms forth
#print axioms total
#print axioms native
end LIBB_PolicyValue
end
