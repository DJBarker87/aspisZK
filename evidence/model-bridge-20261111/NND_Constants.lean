import NND_MasterCarrier
set_option autoImplicit false
namespace NND_Constants
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem zero_key : key (Array.repeat 32#usize 0#u8) = RSL.zero32 := by
 rfl

theorem audit : key r1_pool_adapter.AUDIT_POLICY_BINDING = RSL.AUDIT_POLICY_BINDING := by
 unfold r1_pool_adapter.AUDIT_POLICY_BINDING
 rfl

theorem profile : key r1_pool_adapter.PROFILE_BINDING = RSL.PROFILE_BINDING := by
 unfold r1_pool_adapter.PROFILE_BINDING
 rfl

theorem release : key r1_pool_adapter.RELEASE_BINDING = RSL.RELEASE_BINDING := by
 unfold r1_pool_adapter.RELEASE_BINDING
 rfl

theorem registry_seed : bytes r1_pool_adapter.VERIFIER_REGISTRY_SEED = RSL.SEED_REGISTRY := by
 unfold r1_pool_adapter.VERIFIER_REGISTRY_SEED
 rfl

theorem entry_seed : bytes r1_pool_adapter.VERIFIER_ENTRY_SEED = RSL.SEED_ENTRY := by
 unfold r1_pool_adapter.VERIFIER_ENTRY_SEED
 rfl

theorem registry2_seed : bytes r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED = RSL.SEED_REGISTRY_V2 := by
 unfold r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED
 rfl

theorem entry2_seed : bytes r1_pool_adapter.VERIFIER_ENTRY_V2_SEED = RSL.SEED_ENTRY_V2 := by
 unfold r1_pool_adapter.VERIFIER_ENTRY_V2_SEED
 rfl

theorem master_seed : bytes r1_pool_adapter.PAIR_FOREST_MASTER_SEED = RSL.SEED_MASTER := by
 unfold r1_pool_adapter.PAIR_FOREST_MASTER_SEED
 rfl

theorem checkpoint_seed : bytes r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED = RSL.SEED_CHECKPOINT := by
 unfold r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED
 rfl

theorem lane_seed : bytes r1_pool_adapter.PAIR_FOREST_LANE_SEED = RSL.SEED_LANE := by
 unfold r1_pool_adapter.PAIR_FOREST_LANE_SEED
 rfl

#print axioms zero_key
#print axioms audit
#print axioms profile
#print axioms release
#print axioms registry_seed
#print axioms entry_seed
#print axioms registry2_seed
#print axioms entry2_seed
#print axioms master_seed
#print axioms checkpoint_seed
#print axioms lane_seed
end NND_Constants
