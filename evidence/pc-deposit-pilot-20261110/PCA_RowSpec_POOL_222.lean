import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::PoolV1PairLeafWitnessV1::single_output. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_222 := Digest
abbrev Reply_POOL_222 := PairWitness
def RowSpec_POOL_222
    (native reference : Args_POOL_222 → PCA_State → Execution Reply_POOL_222) : Prop :=
  FullPacket native reference
end PCA
