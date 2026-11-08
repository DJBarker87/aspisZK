import PV_LIB_SPEC_F170PackageComparison
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F170PackagePair
abbrev PackagePre := @PV_FN_THREAD_f170.PreNumbered
abbrev PackageMachineSpec := @PV_FN_THREAD_f170.OriginalMachineSpec
abbrev PackagePost := @PV_FN_THREAD_f170.Post
abbrev PackageContract := @PV_FN_THREAD_f170.OriginalContract
/-- Literal old target and the paired new whole target; neither is presumed
proved. The new target is instantiated by F170Full.Contract in its own cohort. -/
def Comparison {E : Type} (M : PV_FN_W4_ContractEntry.Machine E)
    (base : PV_STX2_Store.Carrier PV_EVHB_OwnerMachine.OWNER PV_STX2_Syntax.Data)
    (D : PV_FN_W4_NativeFootprint.Effects) (newContract : Prop) : Prop :=
  PV_FN_THREAD_f170.OriginalContract M base D ∧ newContract
#print axioms PackagePre
#print axioms PackageMachineSpec
#print axioms PackagePost
#print axioms PackageContract
#print axioms Comparison
end PV_LIB_SPEC_F170PackagePair
