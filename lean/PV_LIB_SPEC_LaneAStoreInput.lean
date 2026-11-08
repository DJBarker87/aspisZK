import PV_LIB_A_StoreActionMachine
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_LaneAStoreInput
open PV_STX2_Syntax
/-- Read-only lane-A input at03c3c72b143. This selects its actual documented
meanings, with no independent Store transformer or full-table parameter.
The imported definition is explicitly PARTIAL; absence is missing semantics. -/
abbrev actions := PV_LIB_StoreActionTable.v2
abbrev interpret := @PV_LIB_StoreActionTable.interpret
/-- Actual lane-A interpreter: OWNER-aware base plus v2 native projections.
BODY-expanded effects are not applied a second time. Unsupported projections
retain their explicit undefined result, without a defined-write premise.
This import is not a certificate of complete D984 coverage or source adequacy. -/
abbrev step := PV_LIB_StoreActionTable.step
abbrev advance := PV_LIB_StoreActionTable.advance
abbrev coverage := PV_LIB_StoreActionTable.coverage
/-- Concrete limitations remain visible to every consumer of this import. -/
theorem limits :
    coverage .cellBoolSet504 = .boolOnly ∧
    coverage .arcNonlast486 = .nonlastOnly ∧
    coverage .weakNonlast683 = .nonlastOnly ∧
    coverage .scopeDecrement611 = .unparkCompositionOpen := ⟨rfl,rfl,rfl,rfl⟩
/-- No replacement interpretation is introduced by the lane-C boundary. -/
theorem exact_table (fn : Data) : actions fn = PV_LIB_StoreActionTable.v2 fn := rfl

#print axioms actions
#print axioms interpret
#print axioms step
#print axioms advance
#print axioms coverage
#print axioms limits
#print axioms exact_table
end PV_LIB_SPEC_LaneAStoreInput
