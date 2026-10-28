import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell01
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 1; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[0]! PV_Src_CanonicalRoots.table.val[0]! = ok PV_Src_CanonicalRoots.table.val[1]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨0,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨1,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨0,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨1,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨0,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell01
