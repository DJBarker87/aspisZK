import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell07
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 7; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[6]! PV_Src_CanonicalRoots.table.val[6]! = ok PV_Src_CanonicalRoots.table.val[7]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨6,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨7,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨6,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨7,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨6,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell07
