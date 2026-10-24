import R1SelectedCircleWeights
import S9TensorRowFiveFactorsV1
set_option autoImplicit false
#check @AspisR1.SelectedCircleWeights.circleWeight_base4
noncomputable section
namespace AspisR1S9CircleTensorGenericV1
open AspisCircleTensorBinding
open AspisR1.SelectedCircleWeights
open AspisR1S9StatementTensorGenericV1
variable {K : Type} [Field K] [NeZero (2 : K)]

def base (x : K) (d : Nat) : K := doubledFactor x (2*d-1)
def lineCoefficient (x : K) (d i : Nat) : K :=
  if i=0 then 1 else if i=1 then base x d else if i=2 then
    doubledFactor (base x d) 1 else base x d*doubledFactor (base x d) 1
def firstCoefficient (x y : K) (i : Nat) : K :=
  if i=0 then 1 else if i=1 then y else if i=2 then x else x*y
def circleTable (x y : K) (d i : Nat) : K :=
  if d=0 then firstCoefficient x y i else lineCoefficient x d i

theorem base_one (x : K) : base x 1=doubledFactor x 1 := rfl
/-- The retained symbolic composition law; no recurrence evaluation. -/
theorem base_next (x : K) (d : Nat) (hd : 1≤d) :
    doubledFactor (base x d) 2=base x (d+1) := by
  unfold base
  rw [←AspisV5FriNaturalBasisRadix4.doubledFactor_add]
  congr 1
  omega

theorem circle_zero (x y : K) (s : Fin 4) :
    circleTable x y 0 s.val=firstFactor x y s := by
  fin_cases s <;> rfl

theorem circle_pos (x y : K) (d : Nat) (hd : 1≤d) (s : Fin 4) :
    circleTable x y d s.val=radixFactor (base x d) s := by
  unfold circleTable
  rw [if_neg (show d≠0 by omega)]
  fin_cases s <;> rfl

/-- The five source-shaped factors are exactly the retained natural-circle
weight at the SAME x/y and symbolic index. Reuses the existing base4 theorem. -/
theorem circle_tensor_eq_circleWeight (x y : K) (j : Fin 1024) :
    tensorRow (circleTable x y) j=
      AspisR1.SelectedCircleWeightModel.circleWeight x y j.val := by
  rw [AspisR1S9TensorRowFiveFactorsV1.tensorRow_eq_five_factors]
  have h64 : j.val/16/4=j.val/64 := by omega
  have h256 : j.val/16/16=j.val/256 := by omega
  have hlast : j.val/256<4 := by have := j.isLt;omega
  rw [h64,h256]
  let s0 : Fin 4 := ⟨j.val%4,Nat.mod_lt _ (by omega)⟩
  let s1 : Fin 4 := ⟨j.val/4%4,Nat.mod_lt _ (by omega)⟩
  let s2 : Fin 4 := ⟨j.val/16%4,Nat.mod_lt _ (by omega)⟩
  let s3 : Fin 4 := ⟨j.val/64%4,Nat.mod_lt _ (by omega)⟩
  let s4 : Fin 4 := ⟨j.val/256,hlast⟩
  rw [circle_zero x y s0,circle_pos x y 1 (by omega) s1,
    circle_pos x y 2 (by omega) s2,circle_pos x y 3 (by omega) s3,
    circle_pos x y 4 (by omega) s4]
  have h2 : base x 2=doubledFactor (doubledFactor x 1) 2 := by
    simpa only [base_one] using (base_next x 1 (by omega)).symm
  have h3 : base x 3=doubledFactor (doubledFactor (doubledFactor x 1) 2) 2 := by
    simpa only [h2] using (base_next x 2 (by omega)).symm
  have h4 : base x 4=doubledFactor (doubledFactor (doubledFactor (doubledFactor x 1) 2) 2) 2 := by
    simpa only [h3] using (base_next x 3 (by omega)).symm
  rw [base_one,h2,h3,h4]
  have hc := circleWeight_base4 x y j
  rw [Nat.mod_eq_of_lt hlast] at hc
  simpa only [s0,s1,s2,s3,s4,mul_assoc] using hc.symm

#print axioms base_next
#print axioms circle_zero
#print axioms circle_pos
#print axioms circle_tensor_eq_circleWeight
end AspisR1S9CircleTensorGenericV1
end
