import PV_FN_THREAD_f170_OriginalStatement
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F170PackageComparison
/-- Literal declarations from W4 ce2f78097fa7; source hash
3a34415dec6bb9c09099fa375b0fdfd9172092cb2ea4ca841243ea1a050c00a7. This partition never imports the new
W3-cohort statement. The paired manifest names its exact counterpart. -/
abbrev PackagePre := @PV_FN_THREAD_f170.PreNumbered
abbrev PackageMachineSpec := @PV_FN_THREAD_f170.OriginalMachineSpec
abbrev PackagePost := @PV_FN_THREAD_f170.Post
abbrev PackageContract := @PV_FN_THREAD_f170.OriginalContract
/-- The complete old contract TYPE is retained by the alias, including all
pending dependency arguments. A newContract parameter is a statement target,
not a proved new row, assumed leaf law or added endpoint hypothesis. -/
def Comparison (newContract : Prop) : Prop := newContract
#print axioms PackagePre
#print axioms PackageMachineSpec
#print axioms PackagePost
#print axioms PackageContract
#print axioms Comparison
end PV_LIB_SPEC_F170PackageComparison
