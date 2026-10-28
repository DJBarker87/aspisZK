import R1Z.PV_RDB2_Layout

/-! Combined focused audit of the new padded-layout transport only.
No suspended callback is imported or re-credited by this module. -/
namespace R1Z.PV_RDB2_Audit
set_option autoImplicit false

theorem padded_layout_transport (limit size count : Nat) :
    PV_RDB2_Layout.historical limit size count =
      PV_RDB2_Layout.deployed limit size count ∧
    (PV_RDB2_Layout.historical limit size count = none ↔
      PV_RDB2_Layout.deployed limit size count = none) :=
  ⟨PV_RDB2_Layout.same_result limit size count,
    PV_RDB2_Layout.same_failure limit size count⟩

#print axioms PV_RDB2_Layout.same_result
#print axioms PV_RDB2_Layout.same_failure
#print axioms padded_layout_transport
end R1Z.PV_RDB2_Audit
