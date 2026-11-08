import PV_FN_THREAD_f2OriginalStatement
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F2PackageComparison
/-- Literal declarations from W4 ce2f78097fa7; source hash
cf14e115a3fa7fea864417a1a55f6b13fbecb4593872532879948daa7388d9d1. This partition never imports the new
W3-cohort statement. The paired manifest names its exact counterpart. -/
abbrev PackagePre := @PV_FN_THREAD_f2Contract.Pre
abbrev PackageMachineSpec := @PV_FN_THREAD_f2Contract.MachineSpecWithOriginal
abbrev PackagePost := @PV_FN_THREAD_f2Contract.Post
abbrev PackageContract := @PV_FN_THREAD_f2Contract.ContractWithOriginal
/-- The complete old contract TYPE is retained by the alias, including all
pending dependency arguments. A newContract parameter is a statement target,
not a proved new row, assumed leaf law or added endpoint hypothesis. -/
def Comparison {E : Type} (M : PV_FN_W4_ContractEntry.Machine E)
    (base : PV_STX2_Store.Carrier PV_EVHB_OwnerMachine.OWNER PV_STX2_Syntax.Data)
    (D : PV_FN_W4_NativeFootprint.Effects) (ctl : PV_STX2_SliceMachine.Control)
    (newContract : Prop) : Prop :=
  PV_FN_THREAD_f2Contract.OriginalBodyContract M base D ctl ∧ newContract
#print axioms PackagePre
#print axioms PackageMachineSpec
#print axioms PackagePost
#print axioms PackageContract
#print axioms Comparison
end PV_LIB_SPEC_F2PackageComparison
