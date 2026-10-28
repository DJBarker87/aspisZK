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
namespace AspisR1.JGv_WeightCells14
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 56=(594654132 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_56
theorem basis1_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 56=(1301329178 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_56
theorem basis2_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 56=(1310394628 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_56
theorem basis3_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 56=(644011783 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_56
theorem basis4_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 56=(133588399 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_56
theorem basis5_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 56=(789112667 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_56
theorem basis6_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 56=(197214720 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_56
theorem basis7_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 56=(2025415880 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_56
theorem basis8_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 56=(864908244 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_56
theorem basis9_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 56=(1825039224 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_56
theorem basis10_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 56=(1945117034 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_56
theorem basis11_56 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 56=(888620327 : F) := by
  change (∏ bit ∈ ({3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_56
theorem initial56_0 : JFn_PendingHistory.sum 56 ⟨0,by decide⟩=583486090 := by rfl
#print axioms initial56_0
theorem cell56_0 : JGv_QueryRows.weights 12 56 ⟨0,by decide⟩=(1251625375 : F) := by
  simp only [JGv_QueryRows.weights,initial56_0,basis0_56,basis1_56,basis2_56,basis3_56,basis4_56,basis5_56,basis6_56,basis7_56,basis8_56,basis9_56,basis10_56,basis11_56,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell56_0
theorem initial56_1 : JFn_PendingHistory.sum 56 ⟨1,by decide⟩=276206717 := by rfl
#print axioms initial56_1
theorem cell56_1 : JGv_QueryRows.weights 12 56 ⟨1,by decide⟩=(1067041542 : F) := by
  simp only [JGv_QueryRows.weights,initial56_1,basis0_56,basis1_56,basis2_56,basis3_56,basis4_56,basis5_56,basis6_56,basis7_56,basis8_56,basis9_56,basis10_56,basis11_56,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell56_1
theorem initial56_2 : JFn_PendingHistory.sum 56 ⟨2,by decide⟩=581871196 := by rfl
#print axioms initial56_2
theorem cell56_2 : JGv_QueryRows.weights 12 56 ⟨2,by decide⟩=(76284164 : F) := by
  simp only [JGv_QueryRows.weights,initial56_2,basis0_56,basis1_56,basis2_56,basis3_56,basis4_56,basis5_56,basis6_56,basis7_56,basis8_56,basis9_56,basis10_56,basis11_56,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell56_2
theorem initial56_3 : JFn_PendingHistory.sum 56 ⟨3,by decide⟩=1524717007 := by rfl
#print axioms initial56_3
theorem cell56_3 : JGv_QueryRows.weights 12 56 ⟨3,by decide⟩=(2018491592 : F) := by
  simp only [JGv_QueryRows.weights,initial56_3,basis0_56,basis1_56,basis2_56,basis3_56,basis4_56,basis5_56,basis6_56,basis7_56,basis8_56,basis9_56,basis10_56,basis11_56,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell56_3
theorem basis0_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 57=(1544547198 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_57
theorem basis1_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 57=(613490950 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_57
theorem basis2_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 57=(1789116555 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_57
theorem basis3_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 57=(1918298897 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_57
theorem basis4_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 57=(1288282264 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_57
theorem basis5_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 57=(1242872320 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_57
theorem basis6_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 57=(653868960 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_57
theorem basis7_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 57=(1332232869 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_57
theorem basis8_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 57=(1242294061 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_57
theorem basis9_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 57=(906373858 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_57
theorem basis10_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 57=(554660670 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_57
theorem basis11_57 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 57=(677731017 : F) := by
  change (∏ bit ∈ ({0,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_57
theorem initial57_0 : JFn_PendingHistory.sum 57 ⟨0,by decide⟩=1780737754 := by rfl
#print axioms initial57_0
theorem cell57_0 : JGv_QueryRows.weights 12 57 ⟨0,by decide⟩=(1565930268 : F) := by
  simp only [JGv_QueryRows.weights,initial57_0,basis0_57,basis1_57,basis2_57,basis3_57,basis4_57,basis5_57,basis6_57,basis7_57,basis8_57,basis9_57,basis10_57,basis11_57,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell57_0
theorem initial57_1 : JFn_PendingHistory.sum 57 ⟨1,by decide⟩=1253710700 := by rfl
#print axioms initial57_1
theorem cell57_1 : JGv_QueryRows.weights 12 57 ⟨1,by decide⟩=(969995660 : F) := by
  simp only [JGv_QueryRows.weights,initial57_1,basis0_57,basis1_57,basis2_57,basis3_57,basis4_57,basis5_57,basis6_57,basis7_57,basis8_57,basis9_57,basis10_57,basis11_57,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell57_1
theorem initial57_2 : JFn_PendingHistory.sum 57 ⟨2,by decide⟩=1205871765 := by rfl
#print axioms initial57_2
theorem cell57_2 : JGv_QueryRows.weights 12 57 ⟨2,by decide⟩=(49680426 : F) := by
  simp only [JGv_QueryRows.weights,initial57_2,basis0_57,basis1_57,basis2_57,basis3_57,basis4_57,basis5_57,basis6_57,basis7_57,basis8_57,basis9_57,basis10_57,basis11_57,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell57_2
theorem initial57_3 : JFn_PendingHistory.sum 57 ⟨3,by decide⟩=830468577 := by rfl
#print axioms initial57_3
theorem cell57_3 : JGv_QueryRows.weights 12 57 ⟨3,by decide⟩=(175831291 : F) := by
  simp only [JGv_QueryRows.weights,initial57_3,basis0_57,basis1_57,basis2_57,basis3_57,basis4_57,basis5_57,basis6_57,basis7_57,basis8_57,basis9_57,basis10_57,basis11_57,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell57_3
theorem basis0_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 58=(1274891791 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x1,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_58
theorem basis1_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 58=(1408453047 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x1,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_58
theorem basis2_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 58=(325974198 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x1,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_58
theorem basis3_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 58=(1979777534 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x1,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_58
theorem basis4_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 58=(1236171936 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x1,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_58
theorem basis5_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 58=(955682168 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x1,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_58
theorem basis6_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 58=(1464190200 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x1,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_58
theorem basis7_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 58=(178798156 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x1,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_58
theorem basis8_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 58=(1325895755 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x1,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_58
theorem basis9_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 58=(563046386 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x1,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_58
theorem basis10_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 58=(1468568603 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x1,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_58
theorem basis11_58 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 58=(1171045127 : F) := by
  change (∏ bit ∈ ({1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x1,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_58
theorem initial58_0 : JFn_PendingHistory.sum 58 ⟨0,by decide⟩=837099947 := by rfl
#print axioms initial58_0
theorem cell58_0 : JGv_QueryRows.weights 12 58 ⟨0,by decide⟩=(1457998661 : F) := by
  simp only [JGv_QueryRows.weights,initial58_0,basis0_58,basis1_58,basis2_58,basis3_58,basis4_58,basis5_58,basis6_58,basis7_58,basis8_58,basis9_58,basis10_58,basis11_58,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell58_0
theorem initial58_1 : JFn_PendingHistory.sum 58 ⟨1,by decide⟩=1579278096 := by rfl
#print axioms initial58_1
theorem cell58_1 : JGv_QueryRows.weights 12 58 ⟨1,by decide⟩=(455879481 : F) := by
  simp only [JGv_QueryRows.weights,initial58_1,basis0_58,basis1_58,basis2_58,basis3_58,basis4_58,basis5_58,basis6_58,basis7_58,basis8_58,basis9_58,basis10_58,basis11_58,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell58_1
theorem initial58_2 : JFn_PendingHistory.sum 58 ⟨2,by decide⟩=983244076 := by rfl
#print axioms initial58_2
theorem cell58_2 : JGv_QueryRows.weights 12 58 ⟨2,by decide⟩=(1834044015 : F) := by
  simp only [JGv_QueryRows.weights,initial58_2,basis0_58,basis1_58,basis2_58,basis3_58,basis4_58,basis5_58,basis6_58,basis7_58,basis8_58,basis9_58,basis10_58,basis11_58,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell58_2
theorem initial58_3 : JFn_PendingHistory.sum 58 ⟨3,by decide⟩=81628231 := by rfl
#print axioms initial58_3
theorem cell58_3 : JGv_QueryRows.weights 12 58 ⟨3,by decide⟩=(914733240 : F) := by
  simp only [JGv_QueryRows.weights,initial58_3,basis0_58,basis1_58,basis2_58,basis3_58,basis4_58,basis5_58,basis6_58,basis7_58,basis8_58,basis9_58,basis10_58,basis11_58,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell58_3
theorem basis0_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 59=(878142464 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_59
theorem basis1_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 59=(798013589 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_59
theorem basis2_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 59=(1387513269 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_59
theorem basis3_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 59=(2001110068 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_59
theorem basis4_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 59=(1080505524 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_59
theorem basis5_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 59=(285765914 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_59
theorem basis6_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 59=(1629811161 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_59
theorem basis7_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 59=(793250267 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_59
theorem basis8_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 59=(615299881 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_59
theorem basis9_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 59=(1417267728 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_59
theorem basis10_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 59=(114730652 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_59
theorem basis11_59 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 59=(1855300094 : F) := by
  change (∏ bit ∈ ({0,1,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_59
theorem initial59_0 : JFn_PendingHistory.sum 59 ⟨0,by decide⟩=1576637415 := by rfl
#print axioms initial59_0
theorem cell59_0 : JGv_QueryRows.weights 12 59 ⟨0,by decide⟩=(1789987840 : F) := by
  simp only [JGv_QueryRows.weights,initial59_0,basis0_59,basis1_59,basis2_59,basis3_59,basis4_59,basis5_59,basis6_59,basis7_59,basis8_59,basis9_59,basis10_59,basis11_59,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell59_0
theorem initial59_1 : JFn_PendingHistory.sum 59 ⟨1,by decide⟩=1666296633 := by rfl
#print axioms initial59_1
theorem cell59_1 : JGv_QueryRows.weights 12 59 ⟨1,by decide⟩=(1327012007 : F) := by
  simp only [JGv_QueryRows.weights,initial59_1,basis0_59,basis1_59,basis2_59,basis3_59,basis4_59,basis5_59,basis6_59,basis7_59,basis8_59,basis9_59,basis10_59,basis11_59,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell59_1
theorem initial59_2 : JFn_PendingHistory.sum 59 ⟨2,by decide⟩=217463890 := by rfl
#print axioms initial59_2
theorem cell59_2 : JGv_QueryRows.weights 12 59 ⟨2,by decide⟩=(850614603 : F) := by
  simp only [JGv_QueryRows.weights,initial59_2,basis0_59,basis1_59,basis2_59,basis3_59,basis4_59,basis5_59,basis6_59,basis7_59,basis8_59,basis9_59,basis10_59,basis11_59,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell59_2
theorem initial59_3 : JFn_PendingHistory.sum 59 ⟨3,by decide⟩=1777644172 := by rfl
#print axioms initial59_3
theorem cell59_3 : JGv_QueryRows.weights 12 59 ⟨3,by decide⟩=(1490104858 : F) := by
  simp only [JGv_QueryRows.weights,initial59_3,basis0_59,basis1_59,basis2_59,basis3_59,basis4_59,basis5_59,basis6_59,basis7_59,basis8_59,basis9_59,basis10_59,basis11_59,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell59_3
end AspisR1.JGv_WeightCells14
end
