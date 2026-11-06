import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::account_is_zeroed_program_page. Class D.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_301 := Nat × Key
abbrev Reply_POOL_301 := Bool
def RowSpec_POOL_301
    (native reference : Args_POOL_301 → PCA_State → Execution Reply_POOL_301) : Prop :=
  FullPacket native reference
end PCA
