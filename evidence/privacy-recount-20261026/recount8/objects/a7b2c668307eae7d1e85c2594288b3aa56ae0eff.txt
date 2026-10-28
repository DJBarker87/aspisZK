import R1Z.ProverRwP7FibreTotal
import R1Z.ProverRwP7NormalizeTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7FibreWide
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
abbrev selected := ProverRwP7FibreInstall.selected

theorem embed (ops : ExternalFuns) (x : U32) :
    ∃ out, (selected ops).op110 x = ok out := by
  change ∃ out, ProverRwDictionaryEmbedding.embed x = ok out
  obtain ⟨r,hr⟩ := ProverRwP7NormalizeTotal.remainder x
  unfold ProverRwDictionaryEmbedding.embed ProverRwDictionaryScalar.qFrom
    ProverRwDictionaryScalar.mFrom
  simp only [hr,bind_tc_ok,AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.QM31.from_cm31]
  obtain ⟨out,ho⟩ := ProverRwP7NormalizeTotal.embed
    ⟨⟨r,AspisR1ProducerRelease47.field.M31.ZERO⟩,AspisR1ProducerRelease47.field.CM31.ZERO⟩
  exact ⟨fromW out,by rw [ho]; rfl⟩

theorem total (ops : ExternalFuns) (i : aspis_core.r0.domain.FibreIndex) :
    letI : ExternalFuns := selected ops
    ∃ p, aspis_core.r0.domain.fibre_point
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField i = ok p := by
  letI : ExternalFuns := selected ops
  apply ProverRwP7FibreTotal.source
  exact embed ops
#print axioms embed
#print axioms total
end R1Z.ProverRwP7FibreWide
