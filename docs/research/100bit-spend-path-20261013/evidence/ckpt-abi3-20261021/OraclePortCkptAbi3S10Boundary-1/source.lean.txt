import OraclePortS10ModelInventory

/-! The landed S10 decision-stage inventory has no checkpoint call site.
This is a checked boundary of that particular inventory, not an assertion
that frozen Rust has no checkpoint or that a future source tree cannot. -/
set_option autoImplicit false
namespace AspisR1.OraclePortCkptAbi3S10Boundary
open OraclePortJoinSplit OraclePortS10ModelInventory

theorem no_checkpoint_site (declaration : String) :
    (⟨.checkpointAbi,declaration⟩ : Site) ∉ inventory := by
  simp [inventory,guardSite,parserSite,querySite,merkleSite,arithmeticSite]

#print axioms no_checkpoint_site
end AspisR1.OraclePortCkptAbi3S10Boundary
