import R1Z.PV_Src_RootZero
set_option autoImplicit false
namespace R1Z.PV_Src_RootCell00
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

/-! Actual source parent cell 0; the mathematical certificate is consumed read-only. -/
theorem source : pool_v1.format.pool_v1_tree_parent
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_Src_RootZero.zero PV_Src_RootZero.zero = ok PV_Src_CanonicalRoots.table.val[0]! := by
  apply PV_Src_PortParent.source
  · exact PV_Src_RootZero.canonical 7 (by decide)
  · exact PV_Src_CanonicalRoots.canonical ⟨0,by decide⟩
  · rw [PV_Src_RootZero.meaning,PV_Src_RootFieldMeaning.source ⟨0,by decide⟩]
    exact PV_RunJoin_RootModel.initial

#print axioms source
end R1Z.PV_Src_RootCell00
