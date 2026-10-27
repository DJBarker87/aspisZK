import FJr_CircleOuterCell
import FJd_PointReference
import R1SelectedCircleWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleLiteral
open AspisCircleTensorBinding
abbrev FK := OraclePortCheckpointAbiC5.K

theorem double (x : FK) : FJd_LoopReference.double x=doubledFactor x 1 := rfl

theorem advance (x : FK) (n : Nat) :
    FJr_CircleInnerLoop.advance x n=doubledFactor x (2*n) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [FJr_CircleInnerLoop.advance,ih,double,double,←AspisV5FriNaturalBasisRadix4.doubledFactor_add,
      ←AspisV5FriNaturalBasisRadix4.doubledFactor_add]
    congr 1
    omega

theorem first (x y : FK) (s : Fin 4) :
    FJr_CircleOuterCell.digit x y 0 s=SelectedCircleWeights.firstFactor x y s := by
  fin_cases s <;> rfl

theorem line (x y : FK) (d : Nat) (hd : 1≤d) (s : Fin 4) :
    FJr_CircleOuterCell.digit x y d s=
      SelectedCircleWeights.radixFactor (doubledFactor x (2*d-1)) s := by
  have base : FJr_CircleInnerLoop.advance (FJd_LoopReference.double x) (d-1)=doubledFactor x (2*d-1) := by
    rw [advance,double,←AspisV5FriNaturalBasisRadix4.doubledFactor_add]
    congr 1
    omega
  unfold FJr_CircleOuterCell.digit
  rw [if_neg (by omega : ¬d=0),base,double]
  fin_cases s <;> rfl

theorem tensor (x y : FK) (j : Fin 1024) :
    FJd_PointReference.tensor (fun d s=>FJr_CircleOuterCell.digit x y d.val s) j=
      SelectedCircleWeightModel.circleWeight x y j.val := by
  unfold FJd_PointReference.tensor
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.val_zero,Fin.val_succ,
    Nat.zero_add,pow_zero,pow_one,show 4^2=16 from by decide,show 4^3=64 from by decide,
    show 4^4=256 from by decide,Nat.div_one,mul_one]
  rw [first,line x y 1 (by omega),line x y 2 (by omega),line x y 3 (by omega),line x y 4 (by omega),
    SelectedCircleWeights.circleWeight_base4]
  have b3 : doubledFactor x 3=doubledFactor (doubledFactor x 1) 2 :=
    AspisV5FriNaturalBasisRadix4.doubledFactor_add x 1 2
  have b5 : doubledFactor x 5=doubledFactor (doubledFactor (doubledFactor x 1) 2) 2 := by
    rw [show (5:Nat)=3+2 from by decide,AspisV5FriNaturalBasisRadix4.doubledFactor_add,b3]
  have b7 : doubledFactor x 7=doubledFactor (doubledFactor (doubledFactor (doubledFactor x 1) 2) 2) 2 := by
    rw [show (7:Nat)=5+2 from by decide,AspisV5FriNaturalBasisRadix4.doubledFactor_add,b5]
  change SelectedCircleWeights.firstFactor x y _ *
    (SelectedCircleWeights.radixFactor (doubledFactor x 1) _ *
    (SelectedCircleWeights.radixFactor (doubledFactor x 3) _ *
    (SelectedCircleWeights.radixFactor (doubledFactor x 5) _ *
      SelectedCircleWeights.radixFactor (doubledFactor x 7) _)))=_
  rw [b3,b5,b7]
  ring

theorem mapped_tensor (x y : FK) (j : Fin 1024) :
    FJd_PointReference.tensor (fun d s=>algebraMap FK OraclePortCheckpointAbiC5.E
      (FJr_CircleOuterCell.digit x y d.val s)) j=
      algebraMap FK OraclePortCheckpointAbiC5.E (SelectedCircleWeightModel.circleWeight x y j.val) := by
  rw [←tensor x y j]
  unfold FJd_PointReference.tensor
  rw [map_prod]

#print axioms mapped_tensor

#print axioms tensor

#print axioms double
#print axioms advance
#print axioms first
#print axioms line
end AspisR1.FJr_CircleLiteral
end
