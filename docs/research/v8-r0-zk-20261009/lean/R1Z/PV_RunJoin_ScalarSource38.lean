import R1Z.PV_RunJoin_FieldData34
import R1Z.ProverRwP6BodyCandidate
import R1Z.ProverCommitScalar48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ScalarSource38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34
variable [ExternalTypes]

theorem release (q : AspisR1ProducerRelease47.field.QM31) (s : U32) :
    AspisR1ProducerRelease47.field.QM31.mul_m31 q s =
      AspisR1ProducerRelease47.scalar_ref q s := by
  simp only [AspisR1ProducerRelease47.field.QM31.mul_m31,
    AspisR1ProducerRelease47.field.CM31.mul_m31,
    AspisR1ProducerRelease47.scalar_ref,bind_assoc_eq,bind_tc_ok]

theorem source (ops : ExternalFuns) (q : Q) (s : U32) :
    @aspis_core.field.QM31.mul_m31 _ (ProverRwP6BodyCandidate.selected ops) q s =
      .ok (PV_RunJoin_FieldData34.source (ProverCommitScalar48.product (old q) s)) := by
  change ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
    (AspisR1ProducerRelease47.field.QM31.mul_m31 (ProverRwDictionaryTower.toQ q) s) = _
  rw [release,← native_source q,(ProverCommitScalar48.source_exact (old q) s).1]
  rfl

theorem complete (ops : ExternalFuns) (q : Q) (s : U32) :
    ∃ out,
      @aspis_core.field.QM31.mul_m31 _ (ProverRwP6BodyCandidate.selected ops) q s = .ok out ∧
      canonical out ∧ value out=value q*ProverCommitScalar48.embed s := by
  refine ⟨_,source ops q s,?_,?_⟩
  · exact (canonical_source _).mpr (ProverCommitScalar48.product_canonical _ _)
  · rw [value_source]
    exact ProverCommitScalar48.product_value (old q) s

#print axioms release
#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_ScalarSource38
