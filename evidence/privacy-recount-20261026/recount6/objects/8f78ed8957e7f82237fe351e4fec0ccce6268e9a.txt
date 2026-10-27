import R1Z.ProverRwP7FibreSource
import R1Z.ProverRwP6ComplexTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7FibreArithmetic
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev mul := ProverRwP7FibreSource.aspis_core.field.CM31.mul
abbrev square := ProverRwP7FibreSource.aspis_core.field.CM31.square

theorem mul_total (a b : C) : ∃ c, mul a b = ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6ComplexTotal.mul (toC a) (toC b)
  change ∃ c, mapResult fromC (AspisR1ProducerRelease47.field.CM31.mul (toC a) (toC b)) = ok c
  exact ⟨fromC c,by rw [hc]; rfl⟩

theorem reduce_total (a : U64) :
    ∃ c, AspisR1ProducerRelease47.field.reduce_u64 a = ok c := by
  simp only [AspisR1ProducerRelease47.field.reduce_u64,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem square_total (a : C) : ∃ c, square a = ok c := by
  unfold square ProverRwP7FibreSource.aspis_core.field.CM31.square
  simp only [ProverRwP7FibreSource.aspis_core.field.P,lift,bind_tc_ok,
    ProverRwP7FibreSource.aspis_core.field.M31.reduce_u64,ProverRwSuccessCtReduce.reduce]
  apply ProverRwP6BindTotal.bind_total _ _ (reduce_total _)
  intro m
  apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.mul _ _)
  intro p
  apply ProverRwP6BindTotal.bind_total _ _ (ProverRwP6BaseTotal.double _)
  intro q
  exact ⟨_,rfl⟩
#print axioms mul_total
#print axioms reduce_total
#print axioms square_total
end R1Z.ProverRwP7FibreArithmetic
