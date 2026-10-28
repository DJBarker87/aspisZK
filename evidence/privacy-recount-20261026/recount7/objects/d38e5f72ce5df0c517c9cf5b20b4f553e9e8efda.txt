import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell03
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 3; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[2]! PV_Src_CanonicalRoots.table.val[2]! = ok PV_Src_CanonicalRoots.table.val[3]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨2,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨3,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨2,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨3,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨2,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell03
