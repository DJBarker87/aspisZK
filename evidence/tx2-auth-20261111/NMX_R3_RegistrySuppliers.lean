import LIBB_PoolLib
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistrySuppliers
/-- These are the fields of the supplied module8 instance, at module7's exact
functions. No PoolLib or DeployedIds fields are constructed here. -/
theorem selected :
 LIBB_PoolLib.library.validatePolicy = LIBB_PoolRegistry.validatePolicy ∧
 LIBB_PoolLib.library.decodeRegistryV1 = LIBB_PoolRegistry.decodeRegistryV1 ∧
 LIBB_PoolLib.library.decodeRegistryV2 = LIBB_PoolRegistry.decodeRegistryV2 ∧
 LIBB_PoolLib.library.decodeEntryV1 = LIBB_PoolRegistry.decodeEntryV1 ∧
 LIBB_PoolLib.library.decodeEntryV2 = LIBB_PoolRegistry.decodeEntryV2 := ⟨rfl,rfl,rfl,rfl,rfl⟩
#print axioms selected
end NMX_R3_RegistrySuppliers
end
