import R1Z.PV_CB3_StagedGammaRank
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_GammaCanonical
open Aeneas Aeneas.Std Result ProverRwFull

theorem raw_canonical (a : Array U32 8#usize)
    (h : ∀ d, d ∈ a.val → d.val < 2147483647) :
    PV_CB3_NormalizeIdentity.Canonical (PV_CB3_StagedUnpack.raw a).c0 ∧
    PV_CB3_NormalizeIdentity.Canonical (PV_CB3_StagedUnpack.raw a).c1 := by
  have hc (i : Fin 8) := h (PV_CB3_StagedIndex.limb a i) (PV_CB3_StagedUnpack.limb_mem a i)
  exact ⟨⟨⟨hc ⟨0,by decide⟩,hc ⟨1,by decide⟩⟩,⟨hc ⟨2,by decide⟩,hc ⟨3,by decide⟩⟩⟩,
    ⟨⟨hc ⟨4,by decide⟩,hc ⟨5,by decide⟩⟩,⟨hc ⟨6,by decide⟩,hc ⟨7,by decide⟩⟩⟩⟩

theorem result_canonical (block : Array U8 32#usize) :
    PV_CB3_NormalizeIdentity.Canonical (PV_CB3_StagedGammaRank.result block).c0 ∧
    PV_CB3_NormalizeIdentity.Canonical (PV_CB3_StagedGammaRank.result block).c1 := by
  apply raw_canonical
  intro d hd
  have h := PV_CB3_StagedValue.kernel_canonical (PV_CB3_StagedWords.words block) d hd
  exact h

theorem normalize_halves (block : Array U8 32#usize) :
    PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31
      (PV_CB3_StagedGammaRank.result block).c0 = ok (PV_CB3_StagedGammaRank.result block).c0 ∧
    PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31
      (PV_CB3_StagedGammaRank.result block).c1 = ok (PV_CB3_StagedGammaRank.result block).c1 := by
  exact ⟨PV_CB3_NormalizeIdentity.source _ (result_canonical block).1,
    PV_CB3_NormalizeIdentity.source _ (result_canonical block).2⟩
#print axioms raw_canonical
#print axioms result_canonical
#print axioms normalize_halves
end R1Z.PV_CB3_GammaCanonical
