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
namespace AspisR1.JGv_WeightCells15
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 60=(1657755575 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_60
theorem basis1_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 60=(1223023784 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_60
theorem basis2_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 60=(357201105 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_60
theorem basis3_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 60=(267315679 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_60
theorem basis4_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 60=(603635244 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_60
theorem basis5_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 60=(867993902 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_60
theorem basis6_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 60=(357919354 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_60
theorem basis7_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 60=(1155419032 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_60
theorem basis8_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 60=(1249345437 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_60
theorem basis9_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 60=(1934426356 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_60
theorem basis10_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 60=(782023535 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_60
theorem basis11_60 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 60=(1107694087 : F) := by
  change (∏ bit ∈ ({2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_60
theorem initial60_0 : JFn_PendingHistory.sum 60 ⟨0,by decide⟩=301289576 := by rfl
#print axioms initial60_0
theorem cell60_0 : JGv_QueryRows.weights 12 60 ⟨0,by decide⟩=(1906310017 : F) := by
  simp only [JGv_QueryRows.weights,initial60_0,basis0_60,basis1_60,basis2_60,basis3_60,basis4_60,basis5_60,basis6_60,basis7_60,basis8_60,basis9_60,basis10_60,basis11_60,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell60_0
theorem initial60_1 : JFn_PendingHistory.sum 60 ⟨1,by decide⟩=379221294 := by rfl
#print axioms initial60_1
theorem cell60_1 : JGv_QueryRows.weights 12 60 ⟨1,by decide⟩=(1922713823 : F) := by
  simp only [JGv_QueryRows.weights,initial60_1,basis0_60,basis1_60,basis2_60,basis3_60,basis4_60,basis5_60,basis6_60,basis7_60,basis8_60,basis9_60,basis10_60,basis11_60,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell60_1
theorem initial60_2 : JFn_PendingHistory.sum 60 ⟨2,by decide⟩=1825123628 := by rfl
#print axioms initial60_2
theorem cell60_2 : JGv_QueryRows.weights 12 60 ⟨2,by decide⟩=(566818147 : F) := by
  simp only [JGv_QueryRows.weights,initial60_2,basis0_60,basis1_60,basis2_60,basis3_60,basis4_60,basis5_60,basis6_60,basis7_60,basis8_60,basis9_60,basis10_60,basis11_60,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell60_2
theorem initial60_3 : JFn_PendingHistory.sum 60 ⟨3,by decide⟩=1353143496 := by rfl
#print axioms initial60_3
theorem cell60_3 : JGv_QueryRows.weights 12 60 ⟨3,by decide⟩=(1183184806 : F) := by
  simp only [JGv_QueryRows.weights,initial60_3,basis0_60,basis1_60,basis2_60,basis3_60,basis4_60,basis5_60,basis6_60,basis7_60,basis8_60,basis9_60,basis10_60,basis11_60,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell60_3
theorem basis0_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 61=(1717770624 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_61
theorem basis1_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 61=(1475649077 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_61
theorem basis2_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 61=(347267759 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_61
theorem basis3_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 61=(2023661754 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_61
theorem basis4_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 61=(1992072032 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_61
theorem basis5_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 61=(928241525 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_61
theorem basis6_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 61=(1304760367 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_61
theorem basis7_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 61=(267675091 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_61
theorem basis8_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 61=(1247429313 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_61
theorem basis9_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 61=(1670617540 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_61
theorem basis10_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 61=(1958059610 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_61
theorem basis11_61 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 61=(922642574 : F) := by
  change (∏ bit ∈ ({0,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_61
theorem initial61_0 : JFn_PendingHistory.sum 61 ⟨0,by decide⟩=1818087377 := by rfl
#print axioms initial61_0
theorem cell61_0 : JGv_QueryRows.weights 12 61 ⟨0,by decide⟩=(1914364795 : F) := by
  simp only [JGv_QueryRows.weights,initial61_0,basis0_61,basis1_61,basis2_61,basis3_61,basis4_61,basis5_61,basis6_61,basis7_61,basis8_61,basis9_61,basis10_61,basis11_61,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell61_0
theorem initial61_1 : JFn_PendingHistory.sum 61 ⟨1,by decide⟩=234435719 := by rfl
#print axioms initial61_1
theorem cell61_1 : JGv_QueryRows.weights 12 61 ⟨1,by decide⟩=(424325553 : F) := by
  simp only [JGv_QueryRows.weights,initial61_1,basis0_61,basis1_61,basis2_61,basis3_61,basis4_61,basis5_61,basis6_61,basis7_61,basis8_61,basis9_61,basis10_61,basis11_61,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell61_1
theorem initial61_2 : JFn_PendingHistory.sum 61 ⟨2,by decide⟩=1474578401 := by rfl
#print axioms initial61_2
theorem cell61_2 : JGv_QueryRows.weights 12 61 ⟨2,by decide⟩=(1379646971 : F) := by
  simp only [JGv_QueryRows.weights,initial61_2,basis0_61,basis1_61,basis2_61,basis3_61,basis4_61,basis5_61,basis6_61,basis7_61,basis8_61,basis9_61,basis10_61,basis11_61,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell61_2
theorem initial61_3 : JFn_PendingHistory.sum 61 ⟨3,by decide⟩=271929601 := by rfl
#print axioms initial61_3
theorem cell61_3 : JGv_QueryRows.weights 12 61 ⟨3,by decide⟩=(638126316 : F) := by
  simp only [JGv_QueryRows.weights,initial61_3,basis0_61,basis1_61,basis2_61,basis3_61,basis4_61,basis5_61,basis6_61,basis7_61,basis8_61,basis9_61,basis10_61,basis11_61,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell61_3
theorem basis0_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 62=(1615941827 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_62
theorem basis1_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 62=(2068074815 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_62
theorem basis2_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 62=(288111427 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_62
theorem basis3_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 62=(308681678 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_62
theorem basis4_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 62=(575164994 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_62
theorem basis5_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 62=(1306019774 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_62
theorem basis6_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 62=(1124951245 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_62
theorem basis7_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 62=(2055152006 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_62
theorem basis8_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 62=(545474739 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_62
theorem basis9_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 62=(553792204 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_62
theorem basis10_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 62=(1581427622 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_62
theorem basis11_62 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 62=(283869960 : F) := by
  change (∏ bit ∈ ({1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_62
theorem initial62_0 : JFn_PendingHistory.sum 62 ⟨0,by decide⟩=1523912250 := by rfl
#print axioms initial62_0
theorem cell62_0 : JGv_QueryRows.weights 12 62 ⟨0,by decide⟩=(302308158 : F) := by
  simp only [JGv_QueryRows.weights,initial62_0,basis0_62,basis1_62,basis2_62,basis3_62,basis4_62,basis5_62,basis6_62,basis7_62,basis8_62,basis9_62,basis10_62,basis11_62,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell62_0
theorem initial62_1 : JFn_PendingHistory.sum 62 ⟨1,by decide⟩=312866993 := by rfl
#print axioms initial62_1
theorem cell62_1 : JGv_QueryRows.weights 12 62 ⟨1,by decide⟩=(1743759608 : F) := by
  simp only [JGv_QueryRows.weights,initial62_1,basis0_62,basis1_62,basis2_62,basis3_62,basis4_62,basis5_62,basis6_62,basis7_62,basis8_62,basis9_62,basis10_62,basis11_62,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell62_1
theorem initial62_2 : JFn_PendingHistory.sum 62 ⟨2,by decide⟩=1949862119 := by rfl
#print axioms initial62_2
theorem cell62_2 : JGv_QueryRows.weights 12 62 ⟨2,by decide⟩=(1973201005 : F) := by
  simp only [JGv_QueryRows.weights,initial62_2,basis0_62,basis1_62,basis2_62,basis3_62,basis4_62,basis5_62,basis6_62,basis7_62,basis8_62,basis9_62,basis10_62,basis11_62,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell62_2
theorem initial62_3 : JFn_PendingHistory.sum 62 ⟨3,by decide⟩=1589077379 := by rfl
#print axioms initial62_3
theorem cell62_3 : JGv_QueryRows.weights 12 62 ⟨3,by decide⟩=(917205379 : F) := by
  simp only [JGv_QueryRows.weights,initial62_3,basis0_62,basis1_62,basis2_62,basis3_62,basis4_62,basis5_62,basis6_62,basis7_62,basis8_62,basis9_62,basis10_62,basis11_62,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell62_3
theorem basis0_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 63=(2075173275 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_63
theorem basis1_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 63=(101994736 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_63
theorem basis2_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 63=(1639964103 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_63
theorem basis3_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 63=(1607418705 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_63
theorem basis4_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 63=(454332651 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_63
theorem basis5_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 63=(674420025 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_63
theorem basis6_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 63=(373757088 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_63
theorem basis7_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 63=(428486822 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_63
theorem basis8_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 63=(478407907 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_63
theorem basis9_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 63=(1695648386 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_63
theorem basis10_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 63=(1741626240 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_63
theorem basis11_63 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 63=(1784192794 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_63
theorem initial63_0 : JFn_PendingHistory.sum 63 ⟨0,by decide⟩=1432735874 := by rfl
#print axioms initial63_0
theorem cell63_0 : JGv_QueryRows.weights 12 63 ⟨0,by decide⟩=(1032067811 : F) := by
  simp only [JGv_QueryRows.weights,initial63_0,basis0_63,basis1_63,basis2_63,basis3_63,basis4_63,basis5_63,basis6_63,basis7_63,basis8_63,basis9_63,basis10_63,basis11_63,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell63_0
theorem initial63_1 : JFn_PendingHistory.sum 63 ⟨1,by decide⟩=893637472 := by rfl
#print axioms initial63_1
theorem cell63_1 : JGv_QueryRows.weights 12 63 ⟨1,by decide⟩=(978430364 : F) := by
  simp only [JGv_QueryRows.weights,initial63_1,basis0_63,basis1_63,basis2_63,basis3_63,basis4_63,basis5_63,basis6_63,basis7_63,basis8_63,basis9_63,basis10_63,basis11_63,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell63_1
theorem initial63_2 : JFn_PendingHistory.sum 63 ⟨2,by decide⟩=1102055191 := by rfl
#print axioms initial63_2
theorem cell63_2 : JGv_QueryRows.weights 12 63 ⟨2,by decide⟩=(1015571073 : F) := by
  simp only [JGv_QueryRows.weights,initial63_2,basis0_63,basis1_63,basis2_63,basis3_63,basis4_63,basis5_63,basis6_63,basis7_63,basis8_63,basis9_63,basis10_63,basis11_63,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell63_2
theorem initial63_3 : JFn_PendingHistory.sum 63 ⟨3,by decide⟩=260579375 := by rfl
#print axioms initial63_3
theorem cell63_3 : JGv_QueryRows.weights 12 63 ⟨3,by decide⟩=(1474296651 : F) := by
  simp only [JGv_QueryRows.weights,initial63_3,basis0_63,basis1_63,basis2_63,basis3_63,basis4_63,basis5_63,basis6_63,basis7_63,basis8_63,basis9_63,basis10_63,basis11_63,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell63_3
end AspisR1.JGv_WeightCells15
end
