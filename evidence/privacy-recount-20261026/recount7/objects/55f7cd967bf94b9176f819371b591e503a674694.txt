import R1Z.ProverRwP7FibrePower
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7NormalizeTotal
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47

theorem remainder (x : U32) : ∃ r, x % field.P = ok r := by
  obtain ⟨r,hr,_⟩ := WP.spec_imp_exists
    (UScalar.rem_spec x (y := field.P) (by rw [field.P]; decide))
  exact ⟨r,hr⟩

theorem word (x : U32) : ∃ r,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () x = ok r := by
  obtain ⟨r,hr⟩ := remainder x
  refine ⟨r,?_⟩
  simp only [field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,hr,bind_tc_ok]

theorem canonical (x : field.QM31) : ∃ y, field.wide_exact.canonical_qm31 x = ok y := by
  unfold field.wide_exact.canonical_qm31
  repeat' (apply ProverRwP6BindTotal.bind_total _ _ (word _); intro _)
  exact ⟨_,rfl⟩

theorem embed (x : field.QM31) : ∃ y, field.wide_exact.WideExact.from_qm31 x = ok y := by
  obtain ⟨y,hy⟩ := canonical x
  exact ⟨⟨y,field.QM31.ZERO⟩,by simp only [field.wide_exact.WideExact.from_qm31,hy,bind_tc_ok]⟩
#print axioms remainder
#print axioms word
#print axioms canonical
#print axioms embed
end R1Z.ProverRwP7NormalizeTotal
