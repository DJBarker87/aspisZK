import NND_RegistryLibrary
set_option autoImplicit false
noncomputable section
namespace NND_RegistryReplies
open Aeneas Aeneas.Std Result AdapterRw NND_ResultTotal

def policy (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :=
 value (NHY_PolicyModel.policy p) (NND_PolicyValue.total p)
def registry1 (b : Slice U8) := value (NJQ_Canonical.registry b) (NND_V1DecoderTotal.registry b)
def registry2 (b : Slice U8) := value (NCX_Install.op33 b) (NND_V2DecoderTotal.registry b)
def entry1 (b : Slice U8) := value (NJQ_Canonical.entry b) (NND_V1DecoderTotal.entry b)
def entry2 (b : Slice U8) := value (NCX_Install.op34 b) (NND_V2DecoderTotal.entry b)

theorem policy_eq (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :
 NHY_PolicyModel.policy p = ok (policy p) := equation _ (NND_PolicyValue.total p)
theorem registry1_eq (b : Slice U8) : NJQ_Canonical.registry b = ok (registry1 b) :=
 equation _ (NND_V1DecoderTotal.registry b)
theorem registry2_eq (b : Slice U8) : NCX_Install.op33 b = ok (registry2 b) :=
 equation _ (NND_V2DecoderTotal.registry b)
theorem entry1_eq (b : Slice U8) : NJQ_Canonical.entry b = ok (entry1 b) :=
 equation _ (NND_V1DecoderTotal.entry b)
theorem entry2_eq (b : Slice U8) : NCX_Install.op34 b = ok (entry2 b) :=
 equation _ (NND_V2DecoderTotal.entry b)

#print axioms policy_eq
#print axioms registry1_eq
#print axioms registry2_eq
#print axioms entry1_eq
#print axioms entry2_eq
end NND_RegistryReplies
end
