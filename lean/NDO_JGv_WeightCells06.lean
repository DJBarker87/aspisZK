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
namespace AspisR1.JGv_WeightCells06
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 24=(1036159080 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_24
theorem basis1_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 24=(634543876 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_24
theorem basis2_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 24=(1250519272 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_24
theorem basis3_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 24=(494855043 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_24
theorem basis4_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 24=(586498360 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_24
theorem basis5_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 24=(1943026231 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_24
theorem basis6_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 24=(833276486 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_24
theorem basis7_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 24=(1302842146 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_24
theorem basis8_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 24=(784977351 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_24
theorem basis9_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 24=(829685066 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_24
theorem basis10_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 24=(1599820542 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_24
theorem basis11_24 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 24=(777935253 : F) := by
  change (∏ bit ∈ ({3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_24
theorem initial24_0 : JFn_PendingHistory.sum 24 ⟨0,by decide⟩=1938176182 := by rfl
#print axioms initial24_0
theorem cell24_0 : JGv_QueryRows.weights 12 24 ⟨0,by decide⟩=(1754721479 : F) := by
  simp only [JGv_QueryRows.weights,initial24_0,basis0_24,basis1_24,basis2_24,basis3_24,basis4_24,basis5_24,basis6_24,basis7_24,basis8_24,basis9_24,basis10_24,basis11_24,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell24_0
theorem initial24_1 : JFn_PendingHistory.sum 24 ⟨1,by decide⟩=878750579 := by rfl
#print axioms initial24_1
theorem cell24_1 : JGv_QueryRows.weights 12 24 ⟨1,by decide⟩=(1785388333 : F) := by
  simp only [JGv_QueryRows.weights,initial24_1,basis0_24,basis1_24,basis2_24,basis3_24,basis4_24,basis5_24,basis6_24,basis7_24,basis8_24,basis9_24,basis10_24,basis11_24,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell24_1
theorem initial24_2 : JFn_PendingHistory.sum 24 ⟨2,by decide⟩=464240492 := by rfl
#print axioms initial24_2
theorem cell24_2 : JGv_QueryRows.weights 12 24 ⟨2,by decide⟩=(1663011867 : F) := by
  simp only [JGv_QueryRows.weights,initial24_2,basis0_24,basis1_24,basis2_24,basis3_24,basis4_24,basis5_24,basis6_24,basis7_24,basis8_24,basis9_24,basis10_24,basis11_24,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell24_2
theorem initial24_3 : JFn_PendingHistory.sum 24 ⟨3,by decide⟩=370464749 := by rfl
#print axioms initial24_3
theorem cell24_3 : JGv_QueryRows.weights 12 24 ⟨3,by decide⟩=(1407510212 : F) := by
  simp only [JGv_QueryRows.weights,initial24_3,basis0_24,basis1_24,basis2_24,basis3_24,basis4_24,basis5_24,basis6_24,basis7_24,basis8_24,basis9_24,basis10_24,basis11_24,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell24_3
theorem basis0_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 25=(437911660 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x0,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_25
theorem basis1_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 25=(723270868 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x0,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_25
theorem basis2_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 25=(20810728 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x0,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_25
theorem basis3_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 25=(149848069 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x0,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_25
theorem basis4_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 25=(1664800296 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x0,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_25
theorem basis5_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 25=(569097898 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x0,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_25
theorem basis6_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 25=(84733930 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x0,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_25
theorem basis7_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 25=(306229926 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x0,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_25
theorem basis8_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 25=(405451135 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x0,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_25
theorem basis9_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 25=(1751711139 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x0,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_25
theorem basis10_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 25=(269247079 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x0,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_25
theorem basis11_25 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 25=(1658306986 : F) := by
  change (∏ bit ∈ ({0,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x0,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_25
theorem initial25_0 : JFn_PendingHistory.sum 25 ⟨0,by decide⟩=1549429475 := by rfl
#print axioms initial25_0
theorem cell25_0 : JGv_QueryRows.weights 12 25 ⟨0,by decide⟩=(424886846 : F) := by
  simp only [JGv_QueryRows.weights,initial25_0,basis0_25,basis1_25,basis2_25,basis3_25,basis4_25,basis5_25,basis6_25,basis7_25,basis8_25,basis9_25,basis10_25,basis11_25,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell25_0
theorem initial25_1 : JFn_PendingHistory.sum 25 ⟨1,by decide⟩=388897123 := by rfl
#print axioms initial25_1
theorem cell25_1 : JGv_QueryRows.weights 12 25 ⟨1,by decide⟩=(60512243 : F) := by
  simp only [JGv_QueryRows.weights,initial25_1,basis0_25,basis1_25,basis2_25,basis3_25,basis4_25,basis5_25,basis6_25,basis7_25,basis8_25,basis9_25,basis10_25,basis11_25,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell25_1
theorem initial25_2 : JFn_PendingHistory.sum 25 ⟨2,by decide⟩=2078928895 := by rfl
#print axioms initial25_2
theorem cell25_2 : JGv_QueryRows.weights 12 25 ⟨2,by decide⟩=(1483301961 : F) := by
  simp only [JGv_QueryRows.weights,initial25_2,basis0_25,basis1_25,basis2_25,basis3_25,basis4_25,basis5_25,basis6_25,basis7_25,basis8_25,basis9_25,basis10_25,basis11_25,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell25_2
theorem initial25_3 : JFn_PendingHistory.sum 25 ⟨3,by decide⟩=614800989 := by rfl
#print axioms initial25_3
theorem cell25_3 : JGv_QueryRows.weights 12 25 ⟨3,by decide⟩=(1414496563 : F) := by
  simp only [JGv_QueryRows.weights,initial25_3,basis0_25,basis1_25,basis2_25,basis3_25,basis4_25,basis5_25,basis6_25,basis7_25,basis8_25,basis9_25,basis10_25,basis11_25,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell25_3
theorem basis0_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 26=(1819445709 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x1,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_26
theorem basis1_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 26=(1444407617 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x1,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_26
theorem basis2_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 26=(597580099 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x1,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_26
theorem basis3_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 26=(1292727541 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x1,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_26
theorem basis4_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 26=(1591904612 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x1,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_26
theorem basis5_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 26=(1603016287 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x1,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_26
theorem basis6_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 26=(1735481316 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x1,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_26
theorem basis7_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 26=(2075124110 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x1,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_26
theorem basis8_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 26=(1631051874 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x1,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_26
theorem basis9_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 26=(1762453003 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x1,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_26
theorem basis10_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 26=(1105221715 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x1,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_26
theorem basis11_26 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 26=(1754804528 : F) := by
  change (∏ bit ∈ ({1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x1,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_26
theorem initial26_0 : JFn_PendingHistory.sum 26 ⟨0,by decide⟩=833455043 := by rfl
#print axioms initial26_0
theorem cell26_0 : JGv_QueryRows.weights 12 26 ⟨0,by decide⟩=(1440730222 : F) := by
  simp only [JGv_QueryRows.weights,initial26_0,basis0_26,basis1_26,basis2_26,basis3_26,basis4_26,basis5_26,basis6_26,basis7_26,basis8_26,basis9_26,basis10_26,basis11_26,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell26_0
theorem initial26_1 : JFn_PendingHistory.sum 26 ⟨1,by decide⟩=2045046271 := by rfl
#print axioms initial26_1
theorem cell26_1 : JGv_QueryRows.weights 12 26 ⟨1,by decide⟩=(1004532686 : F) := by
  simp only [JGv_QueryRows.weights,initial26_1,basis0_26,basis1_26,basis2_26,basis3_26,basis4_26,basis5_26,basis6_26,basis7_26,basis8_26,basis9_26,basis10_26,basis11_26,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell26_1
theorem initial26_2 : JFn_PendingHistory.sum 26 ⟨2,by decide⟩=868333983 := by rfl
#print axioms initial26_2
theorem cell26_2 : JGv_QueryRows.weights 12 26 ⟨2,by decide⟩=(737647431 : F) := by
  simp only [JGv_QueryRows.weights,initial26_2,basis0_26,basis1_26,basis2_26,basis3_26,basis4_26,basis5_26,basis6_26,basis7_26,basis8_26,basis9_26,basis10_26,basis11_26,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell26_2
theorem initial26_3 : JFn_PendingHistory.sum 26 ⟨3,by decide⟩=1954240680 := by rfl
#print axioms initial26_3
theorem cell26_3 : JGv_QueryRows.weights 12 26 ⟨3,by decide⟩=(2112904354 : F) := by
  simp only [JGv_QueryRows.weights,initial26_3,basis0_26,basis1_26,basis2_26,basis3_26,basis4_26,basis5_26,basis6_26,basis7_26,basis8_26,basis9_26,basis10_26,basis11_26,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell26_3
theorem basis0_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 27=(523710896 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_27
theorem basis1_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 27=(2049514443 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_27
theorem basis2_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 27=(451028745 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_27
theorem basis3_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 27=(439063016 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_27
theorem basis4_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 27=(357153821 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_27
theorem basis5_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 27=(867058535 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_27
theorem basis6_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 27=(851892047 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_27
theorem basis7_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 27=(1285192731 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_27
theorem basis8_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 27=(1702127288 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_27
theorem basis9_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 27=(1649658328 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_27
theorem basis10_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 27=(897011458 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_27
theorem basis11_27 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 27=(1151826786 : F) := by
  change (∏ bit ∈ ({0,1,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_27
theorem initial27_0 : JFn_PendingHistory.sum 27 ⟨0,by decide⟩=1176095107 := by rfl
#print axioms initial27_0
theorem cell27_0 : JGv_QueryRows.weights 12 27 ⟨0,by decide⟩=(918979696 : F) := by
  simp only [JGv_QueryRows.weights,initial27_0,basis0_27,basis1_27,basis2_27,basis3_27,basis4_27,basis5_27,basis6_27,basis7_27,basis8_27,basis9_27,basis10_27,basis11_27,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell27_0
theorem initial27_1 : JFn_PendingHistory.sum 27 ⟨1,by decide⟩=327556127 := by rfl
#print axioms initial27_1
theorem cell27_1 : JGv_QueryRows.weights 12 27 ⟨1,by decide⟩=(589592585 : F) := by
  simp only [JGv_QueryRows.weights,initial27_1,basis0_27,basis1_27,basis2_27,basis3_27,basis4_27,basis5_27,basis6_27,basis7_27,basis8_27,basis9_27,basis10_27,basis11_27,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell27_1
theorem initial27_2 : JFn_PendingHistory.sum 27 ⟨2,by decide⟩=2123999433 := by rfl
#print axioms initial27_2
theorem cell27_2 : JGv_QueryRows.weights 12 27 ⟨2,by decide⟩=(1910683429 : F) := by
  simp only [JGv_QueryRows.weights,initial27_2,basis0_27,basis1_27,basis2_27,basis3_27,basis4_27,basis5_27,basis6_27,basis7_27,basis8_27,basis9_27,basis10_27,basis11_27,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell27_2
theorem initial27_3 : JFn_PendingHistory.sum 27 ⟨3,by decide⟩=387369717 := by rfl
#print axioms initial27_3
theorem cell27_3 : JGv_QueryRows.weights 12 27 ⟨3,by decide⟩=(161535737 : F) := by
  simp only [JGv_QueryRows.weights,initial27_3,basis0_27,basis1_27,basis2_27,basis3_27,basis4_27,basis5_27,basis6_27,basis7_27,basis8_27,basis9_27,basis10_27,basis11_27,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell27_3
end AspisR1.JGv_WeightCells06
end
