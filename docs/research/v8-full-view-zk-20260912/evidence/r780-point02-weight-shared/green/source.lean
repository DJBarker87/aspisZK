import AspisV8R19.R780Point02WeightPrototype

namespace AspisV8R19.R780Point02WeightShared
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem w0_at (i : Fin 1024) : w0 i.val = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) i := by
  simp [w0, extendFin1024, i.isLt]
#print axioms w0_at

theorem w2_at (i : Fin 1024) : w2 i.val = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) i := by
  simp [w2, extendFin1024, i.isLt]
#print axioms w2_at
end
end AspisV8R19.R780Point02WeightShared
