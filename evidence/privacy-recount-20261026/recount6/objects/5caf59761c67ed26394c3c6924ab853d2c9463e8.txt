import R1Z.ProverRwP6ComplexTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6QuarticTotal
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
abbrev Q := field.QM31
theorem add (a b : Q) : ∃ c, field.QM31.add a b = ok c := by
  unfold field.QM31.add
  repeat' (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ComplexTotal.add _ _); intro _)
  exact ⟨_,rfl⟩
theorem sub (a b : Q) : ∃ c, field.QM31.sub a b = ok c := by
  unfold field.QM31.sub
  repeat' (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ComplexTotal.sub _ _); intro _)
  exact ⟨_,rfl⟩
theorem mul (a b : Q) : ∃ c, field.QM31.mul a b = ok c := by
  obtain ⟨m0,h0⟩ := ProverRwP6ComplexTotal.mul a.c0 b.c0
  obtain ⟨m1,h1⟩ := ProverRwP6ComplexTotal.mul a.c1 b.c1
  obtain ⟨c,hc⟩ := ProverRwP6ComplexTotal.add a.c0 a.c1
  obtain ⟨d,hd⟩ := ProverRwP6ComplexTotal.add b.c0 b.c1
  obtain ⟨m2,h2⟩ := ProverRwP6ComplexTotal.mul c d
  obtain ⟨r,hr⟩ := ProverRwP6ComplexTotal.mul_by_r m1
  obtain ⟨s,hs⟩ := ProverRwP6ComplexTotal.add m0 r
  obtain ⟨t,ht⟩ := ProverRwP6ComplexTotal.sub m2 m0
  obtain ⟨u,hu⟩ := ProverRwP6ComplexTotal.sub t m1
  simp only [field.QM31.mul,h0,h1,hc,hd,h2,hr,hs,ht,hu,bind_tc_ok]
  exact ⟨_,rfl⟩
theorem mul_u (a : Q) : ∃ c, field.wide_exact.mul_u a = ok c := by
  unfold field.wide_exact.mul_u
  apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6ComplexTotal.mul_by_r _)
  intro c
  exact ⟨_,rfl⟩
#print axioms add
#print axioms sub
#print axioms mul
#print axioms mul_u
end R1Z.ProverRwP6QuarticTotal
