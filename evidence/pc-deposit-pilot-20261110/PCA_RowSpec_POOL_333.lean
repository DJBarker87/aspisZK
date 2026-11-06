import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::require_program_owned_zeroed. Class D.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_333 := Nat × Key × Nat × Rent
abbrev Reply_POOL_333 := Unit
def RowSpec_POOL_333
    (native reference : Args_POOL_333 → PCA_State → Execution Reply_POOL_333) : Prop :=
  FullPacket native reference
end PCA
