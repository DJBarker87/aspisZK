import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell15
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 15; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[14]! PV_Src_CanonicalRoots.table.val[14]! = ok PV_Src_CanonicalRoots.table.val[15]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨14,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨15,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨14,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨15,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨14,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell15
