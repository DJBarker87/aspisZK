import NNH_Libraries
import NNH_MRegistryLibrary
set_option autoImplicit false
noncomputable section
namespace NNH_RegistryLibraryMatch
open RSL NNH_Libraries
/-- Actual library decoder fields agree with the existing model transport's
local source library, at every byte argument; no decoder success premise. -/
theorem registry1 (b : Bytes) : L.decodeRegistryV1 b=NNH_MV1DecoderValues.registry b := by rfl
theorem entry1 (b : Bytes) : L.decodeEntryV1 b=NNH_MV1DecoderValues.entry b := by rfl
theorem registry2 (b : Bytes) : L.decodeRegistryV2 b=NNH_MV2DecoderValues.registry b := by rfl
theorem entry2 (b : Bytes) : L.decodeEntryV2 b=NNH_MV2DecoderValues.entry b := by rfl
theorem policy (p : VerifierPolicy) : L.validatePolicy p=NNH_MPolicyValue.validate p := by rfl
/-- Installing the model transport's five fields leaves actual L unchanged. -/
theorem installed : NNH_MRegistryLibrary.install L=L := by rfl
#print axioms registry1
#print axioms entry1
#print axioms registry2
#print axioms entry2
#print axioms policy
#print axioms installed
end NNH_RegistryLibraryMatch
