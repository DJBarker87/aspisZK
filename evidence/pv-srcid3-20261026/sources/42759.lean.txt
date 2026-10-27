import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell10
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 10; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[9]! PV_Src_CanonicalRoots.table.val[9]! = ok PV_Src_CanonicalRoots.table.val[10]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨9,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨10,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨9,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨10,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨9,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell10
