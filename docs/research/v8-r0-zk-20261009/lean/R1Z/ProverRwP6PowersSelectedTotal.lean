import R1Z.ProverRwP6PowersInstall
import R1Z.ProverRwP6WideTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersSelectedTotal
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev selected := ProverRwP6BoundaryInstall.selected
theorem zero (ops : ExternalFuns) : ∃ c : W, (selected ops).op42 = ok c :=
  ⟨ProverRwDictionaryTower.fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO,rfl⟩
theorem one (ops : ExternalFuns) : ∃ c : W, (selected ops).op91 = ok c :=
  ⟨ProverRwDictionaryTower.fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE,rfl⟩
theorem mul (ops : ExternalFuns) (a b : W) : ∃ c, (selected ops).op47 a b = ok c := by
  change ∃ c, ProverRwDictionaryTower.wMul a b = ok c
  exact ProverRwP6WideTotal.dictionary_mul a b
#print axioms zero
#print axioms one
#print axioms mul
end R1Z.ProverRwP6PowersSelectedTotal
