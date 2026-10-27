import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell11
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 11; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[10]! PV_Src_CanonicalRoots.table.val[10]! = ok PV_Src_CanonicalRoots.table.val[11]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨10,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨11,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨10,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨11,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨10,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell11
