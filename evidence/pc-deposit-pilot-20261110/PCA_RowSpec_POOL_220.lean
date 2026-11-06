import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::PoolV1PairLeafWitnessV1::leaf_digest. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_220 := PairWitness
abbrev Reply_POOL_220 := Digest
def RowSpec_POOL_220
    (native reference : Args_POOL_220 → PCA_State → Execution Reply_POOL_220) : Prop :=
  FullPacket native reference
end PCA
