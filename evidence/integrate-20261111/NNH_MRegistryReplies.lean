import NNH_MRegistryLibrary
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryReplies
open Aeneas Aeneas.Std Result AdapterRw NNH_MResultTotal

def policy (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :=
 value (NHY_PolicyModel.policy p) (NNH_MPolicyValue.total p)
def registry1 (b : Slice U8) := value (NJQ_Canonical.registry b) (NNH_MV1DecoderTotal.registry b)
def registry2 (b : Slice U8) := value (NCX_Install.op33 b) (NNH_MV2DecoderTotal.registry b)
def entry1 (b : Slice U8) := value (NJQ_Canonical.entry b) (NNH_MV1DecoderTotal.entry b)
def entry2 (b : Slice U8) := value (NCX_Install.op34 b) (NNH_MV2DecoderTotal.entry b)

theorem policy_eq (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :
 NHY_PolicyModel.policy p = ok (policy p) := equation _ (NNH_MPolicyValue.total p)
theorem registry1_eq (b : Slice U8) : NJQ_Canonical.registry b = ok (registry1 b) :=
 equation _ (NNH_MV1DecoderTotal.registry b)
theorem registry2_eq (b : Slice U8) : NCX_Install.op33 b = ok (registry2 b) :=
 equation _ (NNH_MV2DecoderTotal.registry b)
theorem entry1_eq (b : Slice U8) : NJQ_Canonical.entry b = ok (entry1 b) :=
 equation _ (NNH_MV1DecoderTotal.entry b)
theorem entry2_eq (b : Slice U8) : NCX_Install.op34 b = ok (entry2 b) :=
 equation _ (NNH_MV2DecoderTotal.entry b)

#print axioms policy_eq
#print axioms registry1_eq
#print axioms registry2_eq
#print axioms entry1_eq
#print axioms entry2_eq
end NNH_MRegistryReplies
end
