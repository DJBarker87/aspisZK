import AspisV8R19.R754Point1GuardedTransport

namespace AspisR19.R755Point1BasisTransport
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R748JointWitnessPointEntry
noncomputable section

theorem w_from_basis (j : Fin 1024) (b : M)
    (hb : sourcePointBasis point (order j).val = b) :
    w j.val = if order j ∈ inactive.erase (1023 : Fin 1024)
      then b + 576 else b := by
  unfold w AspisV8R17.extendFin1024
  rw [dif_pos j.isLt]
  change AspisV8R16.transportDual inactive 1023 order
    (fun k => sourcePointBasis point k.val) j = _
  unfold AspisV8R16.transportDual
  by_cases h : order j ∈ inactive.erase (1023 : Fin 1024)
  · simp only [if_pos h]
    change sourcePointBasis point (order j).val - sourcePointBasis point 1023 = b + 576
    rw [hb, R754Point1GuardedTransport.point1_pivot_basis_neg]
    ring
  · simp only [if_neg h]
    exact hb

#print axioms w_from_basis
end
end AspisR19.R755Point1BasisTransport
