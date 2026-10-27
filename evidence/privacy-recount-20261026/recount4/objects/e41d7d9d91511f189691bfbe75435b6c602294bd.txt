import R1Z.ProverRwP6BaseTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6ComplexTotal
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
abbrev C := field.CM31

theorem add (a b : C) : ∃ c, field.CM31.add a b = ok c := by
  unfold field.CM31.add
  repeat' (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.add _ _); intro _)
  exact ⟨_,rfl⟩
theorem sub (a b : C) : ∃ c, field.CM31.sub a b = ok c := by
  unfold field.CM31.sub
  repeat' (apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.sub _ _); intro _)
  exact ⟨_,rfl⟩
theorem mul (a b : C) : ∃ c, field.CM31.mul a b = ok c := by
  obtain ⟨m0,h0⟩ := ProverRwP6BaseTotal.mul a.a b.a
  obtain ⟨m1,h1⟩ := ProverRwP6BaseTotal.mul a.b b.b
  unfold field.CM31.mul
  simp only [h0,h1,lift,bind_tc_ok]
  apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.reduce _)
  intro m2
  obtain ⟨r,hr⟩ := ProverRwP6BaseTotal.sub m0 m1
  obtain ⟨s,hs⟩ := ProverRwP6BaseTotal.sub m2 m0
  obtain ⟨t,ht⟩ := ProverRwP6BaseTotal.sub s m1
  simp only [hr,hs,ht,bind_tc_ok]
  exact ⟨_,rfl⟩
theorem mul_by_r (a : C) : ∃ c, field.mul_by_r a = ok c := by
  unfold field.mul_by_r
  repeat' first
    | apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.double _); intro _
    | apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.sub _ _); intro _
    | apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.add _ _); intro _
  exact ⟨_,rfl⟩
#print axioms add
#print axioms sub
#print axioms mul
#print axioms mul_by_r
end R1Z.ProverRwP6ComplexTotal
