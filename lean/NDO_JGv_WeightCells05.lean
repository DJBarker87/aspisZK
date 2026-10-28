import NDO_JGv_PowerLimbs
import NDO_JGv_BasisFactors0
import NDO_JGv_BasisFactors1
import NDO_JGv_BasisFactors2
import NDO_JGv_BasisFactors3
import NDO_JGv_BasisFactors4
import NDO_JGv_BasisFactors5
import NDO_JGv_BasisFactors6
import NDO_JGv_BasisFactors7
import NDO_JGv_BasisFactors8
import NDO_JGv_BasisFactors9
import NDO_JGv_BasisFactors10
import NDO_JGv_BasisFactors11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_WeightCells05
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 20=(964148840 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_20
theorem basis1_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 20=(1886058556 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_20
theorem basis2_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 20=(578136502 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_20
theorem basis3_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 20=(1960964177 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_20
theorem basis4_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 20=(1563829369 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_20
theorem basis5_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 20=(813980142 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_20
theorem basis6_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 20=(590114690 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_20
theorem basis7_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 20=(275989817 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_20
theorem basis8_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 20=(357926730 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_20
theorem basis9_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 20=(1004446024 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_20
theorem basis10_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 20=(1951105650 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_20
theorem basis11_20 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 20=(1254600114 : F) := by
  change (∏ bit ∈ ({2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_20
theorem initial20_0 : JFn_PendingHistory.sum 20 ⟨0,by decide⟩=1147110517 := by rfl
#print axioms initial20_0
theorem cell20_0 : JGv_QueryRows.weights 12 20 ⟨0,by decide⟩=(1525774516 : F) := by
  simp only [JGv_QueryRows.weights,initial20_0,basis0_20,basis1_20,basis2_20,basis3_20,basis4_20,basis5_20,basis6_20,basis7_20,basis8_20,basis9_20,basis10_20,basis11_20,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell20_0
theorem initial20_1 : JFn_PendingHistory.sum 20 ⟨1,by decide⟩=1440701546 := by rfl
#print axioms initial20_1
theorem cell20_1 : JGv_QueryRows.weights 12 20 ⟨1,by decide⟩=(2102595507 : F) := by
  simp only [JGv_QueryRows.weights,initial20_1,basis0_20,basis1_20,basis2_20,basis3_20,basis4_20,basis5_20,basis6_20,basis7_20,basis8_20,basis9_20,basis10_20,basis11_20,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell20_1
theorem initial20_2 : JFn_PendingHistory.sum 20 ⟨2,by decide⟩=1879628027 := by rfl
#print axioms initial20_2
theorem cell20_2 : JGv_QueryRows.weights 12 20 ⟨2,by decide⟩=(456713530 : F) := by
  simp only [JGv_QueryRows.weights,initial20_2,basis0_20,basis1_20,basis2_20,basis3_20,basis4_20,basis5_20,basis6_20,basis7_20,basis8_20,basis9_20,basis10_20,basis11_20,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell20_2
theorem initial20_3 : JFn_PendingHistory.sum 20 ⟨3,by decide⟩=784621982 := by rfl
#print axioms initial20_3
theorem cell20_3 : JGv_QueryRows.weights 12 20 ⟨3,by decide⟩=(323302930 : F) := by
  simp only [JGv_QueryRows.weights,initial20_3,basis0_20,basis1_20,basis2_20,basis3_20,basis4_20,basis5_20,basis6_20,basis7_20,basis8_20,basis9_20,basis10_20,basis11_20,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell20_3
theorem basis0_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 21=(1833898761 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x0,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_21
theorem basis1_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 21=(1100076908 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x0,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_21
theorem basis2_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 21=(599416649 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x0,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_21
theorem basis3_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 21=(97194998 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x0,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_21
theorem basis4_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 21=(1237627243 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x0,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_21
theorem basis5_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 21=(423258921 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x0,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_21
theorem basis6_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 21=(1434393966 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x0,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_21
theorem basis7_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 21=(602454948 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x0,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_21
theorem basis8_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 21=(1265548071 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x0,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_21
theorem basis9_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 21=(31397434 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x0,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_21
theorem basis10_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 21=(208034701 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x0,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_21
theorem basis11_21 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 21=(1372793012 : F) := by
  change (∏ bit ∈ ({0,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x0,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_21
theorem initial21_0 : JFn_PendingHistory.sum 21 ⟨0,by decide⟩=500874457 := by rfl
#print axioms initial21_0
theorem cell21_0 : JGv_QueryRows.weights 12 21 ⟨0,by decide⟩=(225125396 : F) := by
  simp only [JGv_QueryRows.weights,initial21_0,basis0_21,basis1_21,basis2_21,basis3_21,basis4_21,basis5_21,basis6_21,basis7_21,basis8_21,basis9_21,basis10_21,basis11_21,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell21_0
theorem initial21_1 : JFn_PendingHistory.sum 21 ⟨1,by decide⟩=105242229 := by rfl
#print axioms initial21_1
theorem cell21_1 : JGv_QueryRows.weights 12 21 ⟨1,by decide⟩=(1899418771 : F) := by
  simp only [JGv_QueryRows.weights,initial21_1,basis0_21,basis1_21,basis2_21,basis3_21,basis4_21,basis5_21,basis6_21,basis7_21,basis8_21,basis9_21,basis10_21,basis11_21,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell21_1
theorem initial21_2 : JFn_PendingHistory.sum 21 ⟨2,by decide⟩=210864545 := by rfl
#print axioms initial21_2
theorem cell21_2 : JGv_QueryRows.weights 12 21 ⟨2,by decide⟩=(858597216 : F) := by
  simp only [JGv_QueryRows.weights,initial21_2,basis0_21,basis1_21,basis2_21,basis3_21,basis4_21,basis5_21,basis6_21,basis7_21,basis8_21,basis9_21,basis10_21,basis11_21,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell21_2
theorem initial21_3 : JFn_PendingHistory.sum 21 ⟨3,by decide⟩=1900165980 := by rfl
#print axioms initial21_3
theorem cell21_3 : JGv_QueryRows.weights 12 21 ⟨3,by decide⟩=(564340588 : F) := by
  simp only [JGv_QueryRows.weights,initial21_3,basis0_21,basis1_21,basis2_21,basis3_21,basis4_21,basis5_21,basis6_21,basis7_21,basis8_21,basis9_21,basis10_21,basis11_21,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell21_3
theorem basis0_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 22=(1386753677 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_22
theorem basis1_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 22=(677523227 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_22
theorem basis2_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 22=(543837446 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_22
theorem basis3_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 22=(1963811241 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_22
theorem basis4_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 22=(1620890956 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_22
theorem basis5_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 22=(618891917 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_22
theorem basis6_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 22=(718520169 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_22
theorem basis7_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 22=(1825088576 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_22
theorem basis8_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 22=(2097952087 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_22
theorem basis9_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 22=(746536134 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_22
theorem basis10_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 22=(1369102278 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_22
theorem basis11_22 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 22=(177588932 : F) := by
  change (∏ bit ∈ ({1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_22
theorem initial22_0 : JFn_PendingHistory.sum 22 ⟨0,by decide⟩=1880987440 := by rfl
#print axioms initial22_0
theorem cell22_0 : JGv_QueryRows.weights 12 22 ⟨0,by decide⟩=(363910681 : F) := by
  simp only [JGv_QueryRows.weights,initial22_0,basis0_22,basis1_22,basis2_22,basis3_22,basis4_22,basis5_22,basis6_22,basis7_22,basis8_22,basis9_22,basis10_22,basis11_22,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell22_0
theorem initial22_1 : JFn_PendingHistory.sum 22 ⟨1,by decide⟩=351555345 := by rfl
#print axioms initial22_1
theorem cell22_1 : JGv_QueryRows.weights 12 22 ⟨1,by decide⟩=(473835524 : F) := by
  simp only [JGv_QueryRows.weights,initial22_1,basis0_22,basis1_22,basis2_22,basis3_22,basis4_22,basis5_22,basis6_22,basis7_22,basis8_22,basis9_22,basis10_22,basis11_22,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell22_1
theorem initial22_2 : JFn_PendingHistory.sum 22 ⟨2,by decide⟩=280103724 := by rfl
#print axioms initial22_2
theorem cell22_2 : JGv_QueryRows.weights 12 22 ⟨2,by decide⟩=(1236156915 : F) := by
  simp only [JGv_QueryRows.weights,initial22_2,basis0_22,basis1_22,basis2_22,basis3_22,basis4_22,basis5_22,basis6_22,basis7_22,basis8_22,basis9_22,basis10_22,basis11_22,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell22_2
theorem initial22_3 : JFn_PendingHistory.sum 22 ⟨3,by decide⟩=1330148876 := by rfl
#print axioms initial22_3
theorem cell22_3 : JGv_QueryRows.weights 12 22 ⟨3,by decide⟩=(663787863 : F) := by
  simp only [JGv_QueryRows.weights,initial22_3,basis0_22,basis1_22,basis2_22,basis3_22,basis4_22,basis5_22,basis6_22,basis7_22,basis8_22,basis9_22,basis10_22,basis11_22,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell22_3
theorem basis0_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 23=(1318368855 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_23
theorem basis1_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 23=(302924704 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_23
theorem basis2_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 23=(763841098 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_23
theorem basis3_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 23=(818126005 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_23
theorem basis4_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 23=(1569182700 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_23
theorem basis5_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 23=(1027323308 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_23
theorem basis6_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 23=(374582826 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_23
theorem basis7_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 23=(820790316 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_23
theorem basis8_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 23=(219552629 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_23
theorem basis9_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 23=(1262295725 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_23
theorem basis10_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 23=(1157625426 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_23
theorem basis11_23 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 23=(142772180 : F) := by
  change (∏ bit ∈ ({0,1,2,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_23
theorem initial23_0 : JFn_PendingHistory.sum 23 ⟨0,by decide⟩=1087467590 := by rfl
#print axioms initial23_0
theorem cell23_0 : JGv_QueryRows.weights 12 23 ⟨0,by decide⟩=(1928075435 : F) := by
  simp only [JGv_QueryRows.weights,initial23_0,basis0_23,basis1_23,basis2_23,basis3_23,basis4_23,basis5_23,basis6_23,basis7_23,basis8_23,basis9_23,basis10_23,basis11_23,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell23_0
theorem initial23_1 : JFn_PendingHistory.sum 23 ⟨1,by decide⟩=1167070157 := by rfl
#print axioms initial23_1
theorem cell23_1 : JGv_QueryRows.weights 12 23 ⟨1,by decide⟩=(1406339318 : F) := by
  simp only [JGv_QueryRows.weights,initial23_1,basis0_23,basis1_23,basis2_23,basis3_23,basis4_23,basis5_23,basis6_23,basis7_23,basis8_23,basis9_23,basis10_23,basis11_23,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell23_1
theorem initial23_2 : JFn_PendingHistory.sum 23 ⟨2,by decide⟩=218265742 := by rfl
#print axioms initial23_2
theorem cell23_2 : JGv_QueryRows.weights 12 23 ⟨2,by decide⟩=(458917871 : F) := by
  simp only [JGv_QueryRows.weights,initial23_2,basis0_23,basis1_23,basis2_23,basis3_23,basis4_23,basis5_23,basis6_23,basis7_23,basis8_23,basis9_23,basis10_23,basis11_23,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell23_2
theorem initial23_3 : JFn_PendingHistory.sum 23 ⟨3,by decide⟩=768893347 := by rfl
#print axioms initial23_3
theorem cell23_3 : JGv_QueryRows.weights 12 23 ⟨3,by decide⟩=(990737347 : F) := by
  simp only [JGv_QueryRows.weights,initial23_3,basis0_23,basis1_23,basis2_23,basis3_23,basis4_23,basis5_23,basis6_23,basis7_23,basis8_23,basis9_23,basis10_23,basis11_23,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell23_3
end AspisR1.JGv_WeightCells05
end
