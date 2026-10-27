import RPu_FJj_HornerInstances
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_HornerConcrete
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (f : Fin 4 → FE) (a : FE) :
    FJj_HornerInstances.horner f a=FJg_LowHorner.horner f a := by
  exact FJj_HornerInstances.tower AspisWideTower.wideU 0 f a
#print axioms value
end AspisR1.FJj_HornerConcrete
end
