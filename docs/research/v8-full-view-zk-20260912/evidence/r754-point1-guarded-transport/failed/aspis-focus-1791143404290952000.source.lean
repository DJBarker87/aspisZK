import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R752SharedWitnessPointSupport

namespace AspisR19.R754Point1GuardedTransport
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable

abbrev M := ZMod 2147483647

lemma point1_pivot_basis :
    sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point 1023 =
      (2147483071 : M) := by
  rw [AspisV8R19.R748JointWitnessPointEntry.point_eq_p]
  rw [AspisR19.FullPointFunctional.source_tensor]
  norm_num [AspisR19.ResidualModel.tensor,
    AspisV8R19.R748JointWitnessPointEntry.p, Fin.prod_univ_succ] <;> decide

lemma point1_pivot_basis_neg :
    sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point 1023 =
      (-576 : M) := by
  rw [point1_pivot_basis]
  norm_num <;> decide

theorem w_guarded (j : Fin 1024)
    (hbits : (((((order j).val >>> 9) &&& 1) = 0) ∨
      (((order j).val >>> 8) &&& 1) = 0)) :
    AspisV8R19.R748JointWitnessPointEntry.w j.val =
      (if order j ∈ inactive.erase (1023 : Fin 1024)
       then (576 : M) else 0) := by
  have hzero := AspisR19.R752SharedWitnessPointSupport.point1_source_basis_zero
    ((order j).val) hbits
  unfold AspisV8R19.R748JointWitnessPointEntry.w AspisV8R17.extendFin1024
  rw [dif_pos j.isLt]
  change AspisV8R16.transportDual inactive 1023 order
      (fun k => sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point k.val) j = _
  unfold AspisV8R16.transportDual
  by_cases h : order j ∈ inactive.erase (1023 : Fin 1024)
  · rw [if_pos h]
    change sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point
        (order j).val - sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point 1023 = 576
    rw [hzero, point1_pivot_basis_neg]
    ring
  · rw [if_neg h]
    change sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point
        (order j).val = 0
    exact hzero

#print axioms point1_pivot_basis
#print axioms point1_pivot_basis_neg
#print axioms w_guarded
end AspisR19.R754Point1GuardedTransport
