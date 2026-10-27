import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell20
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 20; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_CanonicalRoots.table.val[19]! PV_Src_CanonicalRoots.table.val[19]! = ok PV_Src_CanonicalRoots.table.val[20]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_CanonicalRoots.canonical ⟨19,by decide⟩ 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨20,by decide⟩
  · rw [PV_Src_RootFieldMeaning.source ⟨19,by decide⟩,
      PV_Src_RootFieldMeaning.source ⟨20,by decide⟩]
    exact PV_RunJoin_RootModel.parents ⟨19,by decide⟩

#print axioms source
end R1Z.PV_Src_RootCell20
