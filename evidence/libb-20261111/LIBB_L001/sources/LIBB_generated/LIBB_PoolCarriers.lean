import LIB_PoolCarriers
set_option autoImplicit false
namespace LIBB_PoolCarriers
abbrev Request := LIB_PoolCarriers.Request
abbrev Statement := LIB_PoolCarriers.Statement
abbrev Afterstate := LIB_PoolCarriers.Afterstate
abbrev master := LIB_PoolCarriers.master
abbrev checkpoint := LIB_PoolCarriers.checkpoint
abbrev policy := LIB_PoolCarriers.policy
abbrev registryV1 := LIB_PoolCarriers.registryV1
abbrev registryV2 := LIB_PoolCarriers.registryV2
abbrev entryV1 := LIB_PoolCarriers.entryV1
abbrev entryV2 := LIB_PoolCarriers.entryV2
/-- The selected carriers are exactly the merged module-6 carriers. -/
theorem exact_carriers :
    Request = LIB_PoolCarriers.Request ∧
    Statement = LIB_PoolCarriers.Statement ∧
    Afterstate = LIB_PoolCarriers.Afterstate := ⟨rfl, rfl, rfl⟩
#print axioms exact_carriers
end LIBB_PoolCarriers
