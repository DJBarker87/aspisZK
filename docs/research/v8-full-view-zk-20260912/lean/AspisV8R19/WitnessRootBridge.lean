/- Generated one-step certificate. Do not unfold the full root recurrence. -/
import AspisV8R19.WitnessRootStep01
import AspisV8R19.WitnessRootStep02
import AspisV8R19.WitnessRootStep03
import AspisV8R19.WitnessRootStep04
import AspisV8R19.WitnessRootStep05
import AspisV8R19.WitnessRootStep06
import AspisV8R19.WitnessRootStep07
import AspisV8R19.WitnessRootStep08
import AspisV8R19.WitnessRootStep09
import AspisV8R19.WitnessRootStep10
import AspisV8R19.WitnessRootStep11
import AspisV8R19.WitnessRootStep12
import AspisV8R19.WitnessRootStep13
import AspisV8R19.WitnessRootStep14
import AspisV8R19.WitnessRootStep15
import AspisV8R19.WitnessRootStep16
import AspisV8R19.WitnessRootStep17
import AspisV8R19.WitnessRootStep18
import AspisV8R19.WitnessRootStep19
import AspisV8R19.WitnessRootStep20
import AspisV8R19.WitnessRootStep21
import AspisV8R19.WitnessRootStep22
import AspisV8R19.WitnessShiftStep1
import AspisV8R19.WitnessShiftStep2
import AspisV8R19.WitnessShiftStep3
import AspisV8R19.WitnessShiftStep4
namespace AspisR19.WitnessRootData
open RootCertificate ResidualModel SourceResidualPolynomial
noncomputable section
def roots : Fin 22 → M := fun i => (i.val+1:Nat)
theorem roots_list : List.ofFn roots=([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]:List M) := by decide
theorem initial_vector : (fun j : Fin 27 => if j.val=0 then (1:M) else 0)=p0 := by
  funext j
  fin_cases j <;> decide
theorem root_chain : rootRun half (List.ofFn roots) p0=p22 := by
  rw [roots_list]
  apply root_step half 1 _ p0 p1 p22 (fun j => congrFun rootStep01 j)
  apply root_step half 2 _ p1 p2 p22 (fun j => congrFun rootStep02 j)
  apply root_step half 3 _ p2 p3 p22 (fun j => congrFun rootStep03 j)
  apply root_step half 4 _ p3 p4 p22 (fun j => congrFun rootStep04 j)
  apply root_step half 5 _ p4 p5 p22 (fun j => congrFun rootStep05 j)
  apply root_step half 6 _ p5 p6 p22 (fun j => congrFun rootStep06 j)
  apply root_step half 7 _ p6 p7 p22 (fun j => congrFun rootStep07 j)
  apply root_step half 8 _ p7 p8 p22 (fun j => congrFun rootStep08 j)
  apply root_step half 9 _ p8 p9 p22 (fun j => congrFun rootStep09 j)
  apply root_step half 10 _ p9 p10 p22 (fun j => congrFun rootStep10 j)
  apply root_step half 11 _ p10 p11 p22 (fun j => congrFun rootStep11 j)
  apply root_step half 12 _ p11 p12 p22 (fun j => congrFun rootStep12 j)
  apply root_step half 13 _ p12 p13 p22 (fun j => congrFun rootStep13 j)
  apply root_step half 14 _ p13 p14 p22 (fun j => congrFun rootStep14 j)
  apply root_step half 15 _ p14 p15 p22 (fun j => congrFun rootStep15 j)
  apply root_step half 16 _ p15 p16 p22 (fun j => congrFun rootStep16 j)
  apply root_step half 17 _ p16 p17 p22 (fun j => congrFun rootStep17 j)
  apply root_step half 18 _ p17 p18 p22 (fun j => congrFun rootStep18 j)
  apply root_step half 19 _ p18 p19 p22 (fun j => congrFun rootStep19 j)
  apply root_step half 20 _ p19 p20 p22 (fun j => congrFun rootStep20 j)
  apply root_step half 21 _ p20 p21 p22 (fun j => congrFun rootStep21 j)
  apply root_step half 22 _ p21 p22 p22 (fun j => congrFun rootStep22 j)
  rfl
theorem root_coefficients (j : Fin 23) : rootCoefficients half roots j=p22 ⟨j.val,by omega⟩ := by
  unfold rootCoefficients
  rw [initial_vector,root_chain]
theorem shift0 : shift half 0 p22=s0 := rfl
theorem shift1 : shift half 1 p22=s1 :=
  shift_step half 0 p22 s0 s1 shift0 (fun r => congrFun shiftStep1 r)
theorem shift2 : shift half 2 p22=s2 :=
  shift_step half 1 p22 s1 s2 shift1 (fun r => congrFun shiftStep2 r)
theorem shift3 : shift half 3 p22=s3 :=
  shift_step half 2 p22 s2 s3 shift2 (fun r => congrFun shiftStep3 r)
theorem shift4 : shift half 4 p22=s4 :=
  shift_step half 3 p22 s3 s4 shift3 (fun r => congrFun shiftStep4 r)
#print axioms roots_list
#print axioms initial_vector
#print axioms root_chain
#print axioms root_coefficients
#print axioms shift0
#print axioms shift1
#print axioms shift2
#print axioms shift3
#print axioms shift4
end
end AspisR19.WitnessRootData
