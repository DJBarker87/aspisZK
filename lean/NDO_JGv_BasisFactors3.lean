import NDO_JFz_TX2_ChainStep
import S7JoinBasisMachine
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_BasisFactors3
open Aeneas Aeneas.Std
abbrev F := ZMod 2147483647
def x0 : F := 391651885
theorem factor0 : AspisCircleTensorBinding.doubledFactor
    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 0=x0 := by
  rfl
#print axioms factor0
def x1 : F := 998492607
theorem factor1 : AspisCircleTensorBinding.doubledFactor
    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 1=x1 := by
  change 2*(AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 0)^2-1=x1
  rw [factor0]
  norm_num [x0,x1]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms factor1
def x2 : F := 2085028953
theorem factor2 : AspisCircleTensorBinding.doubledFactor
    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 2=x2 := by
  change 2*(AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 1)^2-1=x2
  rw [factor1]
  norm_num [x1,x2]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms factor2
def x3 : F := 875908489
theorem factor3 : AspisCircleTensorBinding.doubledFactor
    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 3=x3 := by
  change 2*(AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 2)^2-1=x3
  rw [factor2]
  norm_num [x2,x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms factor3
def x4 : F := 1593979140
theorem factor4 : AspisCircleTensorBinding.doubledFactor
    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 4=x4 := by
  change 2*(AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 3)^2-1=x4
  rw [factor3]
  norm_num [x3,x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms factor4
def x5 : F := 401576375
theorem factor5 : AspisCircleTensorBinding.doubledFactor
    (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 5=x5 := by
  change 2*(AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 4)^2-1=x5
  rw [factor4]
  norm_num [x4,x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms factor5
end AspisR1.JGv_BasisFactors3
end
