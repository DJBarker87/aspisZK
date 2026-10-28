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
namespace AspisR1.JGv_WeightCells13
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 52=(487795733 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_52
theorem basis1_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 52=(1959520764 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_52
theorem basis2_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 52=(1249310165 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_52
theorem basis3_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 52=(1058735875 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_52
theorem basis4_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 52=(1435513371 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_52
theorem basis5_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 52=(1137804630 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_52
theorem basis6_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 52=(1353275278 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_52
theorem basis7_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 52=(2118431209 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_52
theorem basis8_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 52=(1482348931 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_52
theorem basis9_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 52=(2124783109 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_52
theorem basis10_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 52=(86624082 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_52
theorem basis11_52 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 52=(41162462 : F) := by
  change (∏ bit ∈ ({2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_52
theorem initial52_0 : JFn_PendingHistory.sum 52 ⟨0,by decide⟩=1778388959 := by rfl
#print axioms initial52_0
theorem cell52_0 : JGv_QueryRows.weights 12 52 ⟨0,by decide⟩=(444594168 : F) := by
  simp only [JGv_QueryRows.weights,initial52_0,basis0_52,basis1_52,basis2_52,basis3_52,basis4_52,basis5_52,basis6_52,basis7_52,basis8_52,basis9_52,basis10_52,basis11_52,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell52_0
theorem initial52_1 : JFn_PendingHistory.sum 52 ⟨1,by decide⟩=757436448 := by rfl
#print axioms initial52_1
theorem cell52_1 : JGv_QueryRows.weights 12 52 ⟨1,by decide⟩=(1601956586 : F) := by
  simp only [JGv_QueryRows.weights,initial52_1,basis0_52,basis1_52,basis2_52,basis3_52,basis4_52,basis5_52,basis6_52,basis7_52,basis8_52,basis9_52,basis10_52,basis11_52,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell52_1
theorem initial52_2 : JFn_PendingHistory.sum 52 ⟨2,by decide⟩=1589763598 := by rfl
#print axioms initial52_2
theorem cell52_2 : JGv_QueryRows.weights 12 52 ⟨2,by decide⟩=(488197376 : F) := by
  simp only [JGv_QueryRows.weights,initial52_2,basis0_52,basis1_52,basis2_52,basis3_52,basis4_52,basis5_52,basis6_52,basis7_52,basis8_52,basis9_52,basis10_52,basis11_52,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell52_2
theorem initial52_3 : JFn_PendingHistory.sum 52 ⟨3,by decide⟩=1955873460 := by rfl
#print axioms initial52_3
theorem cell52_3 : JGv_QueryRows.weights 12 52 ⟨3,by decide⟩=(1992625325 : F) := by
  simp only [JGv_QueryRows.weights,initial52_3,basis0_52,basis1_52,basis2_52,basis3_52,basis4_52,basis5_52,basis6_52,basis7_52,basis8_52,basis9_52,basis10_52,basis11_52,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell52_3
theorem basis0_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 53=(910024688 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_53
theorem basis1_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 53=(1158544286 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_53
theorem basis2_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 53=(296460776 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_53
theorem basis3_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 53=(1748561975 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_53
theorem basis4_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 53=(1982603602 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_53
theorem basis5_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 53=(1916114072 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_53
theorem basis6_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 53=(1401154570 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_53
theorem basis7_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 53=(733627661 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_53
theorem basis8_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 53=(1388055039 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_53
theorem basis9_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 53=(1980774436 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_53
theorem basis10_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 53=(549465235 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_53
theorem basis11_53 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 53=(1949757047 : F) := by
  change (∏ bit ∈ ({0,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_53
theorem initial53_0 : JFn_PendingHistory.sum 53 ⟨0,by decide⟩=491670158 := by rfl
#print axioms initial53_0
theorem cell53_0 : JGv_QueryRows.weights 12 53 ⟨0,by decide⟩=(1624643229 : F) := by
  simp only [JGv_QueryRows.weights,initial53_0,basis0_53,basis1_53,basis2_53,basis3_53,basis4_53,basis5_53,basis6_53,basis7_53,basis8_53,basis9_53,basis10_53,basis11_53,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell53_0
theorem initial53_1 : JFn_PendingHistory.sum 53 ⟨1,by decide⟩=1890964609 := by rfl
#print axioms initial53_1
theorem cell53_1 : JGv_QueryRows.weights 12 53 ⟨1,by decide⟩=(484856514 : F) := by
  simp only [JGv_QueryRows.weights,initial53_1,basis0_53,basis1_53,basis2_53,basis3_53,basis4_53,basis5_53,basis6_53,basis7_53,basis8_53,basis9_53,basis10_53,basis11_53,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell53_1
theorem initial53_2 : JFn_PendingHistory.sum 53 ⟨2,by decide⟩=2035659000 := by rfl
#print axioms initial53_2
theorem cell53_2 : JGv_QueryRows.weights 12 53 ⟨2,by decide⟩=(1688660089 : F) := by
  simp only [JGv_QueryRows.weights,initial53_2,basis0_53,basis1_53,basis2_53,basis3_53,basis4_53,basis5_53,basis6_53,basis7_53,basis8_53,basis9_53,basis10_53,basis11_53,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell53_2
theorem initial53_3 : JFn_PendingHistory.sum 53 ⟨3,by decide⟩=544890737 := by rfl
#print axioms initial53_3
theorem cell53_3 : JGv_QueryRows.weights 12 53 ⟨3,by decide⟩=(488016984 : F) := by
  simp only [JGv_QueryRows.weights,initial53_3,basis0_53,basis1_53,basis2_53,basis3_53,basis4_53,basis5_53,basis6_53,basis7_53,basis8_53,basis9_53,basis10_53,basis11_53,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell53_3
theorem basis0_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 54=(1950392480 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_54
theorem basis1_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 54=(828981714 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_54
theorem basis2_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 54=(856745616 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_54
theorem basis3_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 54=(848037016 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_54
theorem basis4_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 54=(1835612582 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_54
theorem basis5_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 54=(1038313416 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_54
theorem basis6_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 54=(945839706 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_54
theorem basis7_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 54=(1735727483 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_54
theorem basis8_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 54=(148747979 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_54
theorem basis9_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 54=(181867240 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_54
theorem basis10_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 54=(221749327 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_54
theorem basis11_54 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 54=(1299065198 : F) := by
  change (∏ bit ∈ ({1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_54
theorem initial54_0 : JFn_PendingHistory.sum 54 ⟨0,by decide⟩=1740694871 := by rfl
#print axioms initial54_0
theorem cell54_0 : JGv_QueryRows.weights 12 54 ⟨0,by decide⟩=(1142683895 : F) := by
  simp only [JGv_QueryRows.weights,initial54_0,basis0_54,basis1_54,basis2_54,basis3_54,basis4_54,basis5_54,basis6_54,basis7_54,basis8_54,basis9_54,basis10_54,basis11_54,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell54_0
theorem initial54_1 : JFn_PendingHistory.sum 54 ⟨1,by decide⟩=192126017 := by rfl
#print axioms initial54_1
theorem cell54_1 : JGv_QueryRows.weights 12 54 ⟨1,by decide⟩=(2118891873 : F) := by
  simp only [JGv_QueryRows.weights,initial54_1,basis0_54,basis1_54,basis2_54,basis3_54,basis4_54,basis5_54,basis6_54,basis7_54,basis8_54,basis9_54,basis10_54,basis11_54,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell54_1
theorem initial54_2 : JFn_PendingHistory.sum 54 ⟨2,by decide⟩=43512142 := by rfl
#print axioms initial54_2
theorem cell54_2 : JGv_QueryRows.weights 12 54 ⟨2,by decide⟩=(317372233 : F) := by
  simp only [JGv_QueryRows.weights,initial54_2,basis0_54,basis1_54,basis2_54,basis3_54,basis4_54,basis5_54,basis6_54,basis7_54,basis8_54,basis9_54,basis10_54,basis11_54,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell54_2
theorem initial54_3 : JFn_PendingHistory.sum 54 ⟨3,by decide⟩=1005157139 := by rfl
#print axioms initial54_3
theorem cell54_3 : JGv_QueryRows.weights 12 54 ⟨3,by decide⟩=(1853275307 : F) := by
  simp only [JGv_QueryRows.weights,initial54_3,basis0_54,basis1_54,basis2_54,basis3_54,basis4_54,basis5_54,basis6_54,basis7_54,basis8_54,basis9_54,basis10_54,basis11_54,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell54_3
theorem basis0_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 55=(560045570 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor4,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x4,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_55
theorem basis1_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 55=(1372752353 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor4,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x4,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_55
theorem basis2_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 55=(174907462 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor4,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x4,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_55
theorem basis3_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 55=(1085338957 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor4,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x4,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_55
theorem basis4_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 55=(1990276139 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor4,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x4,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_55
theorem basis5_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 55=(176039650 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor4,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x4,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_55
theorem basis6_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 55=(179604394 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor4,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x4,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_55
theorem basis7_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 55=(1019028661 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor4,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x4,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_55
theorem basis8_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 55=(1292584980 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor4,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x4,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_55
theorem basis9_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 55=(1685713760 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor4,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x4,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_55
theorem basis10_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 55=(1494945525 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor4,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x4,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_55
theorem basis11_55 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 55=(215903655 : F) := by
  change (∏ bit ∈ ({0,1,2,4,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor4,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x4,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_55
theorem initial55_0 : JFn_PendingHistory.sum 55 ⟨0,by decide⟩=197076199 := by rfl
#print axioms initial55_0
theorem cell55_0 : JGv_QueryRows.weights 12 55 ⟨0,by decide⟩=(1750556686 : F) := by
  simp only [JGv_QueryRows.weights,initial55_0,basis0_55,basis1_55,basis2_55,basis3_55,basis4_55,basis5_55,basis6_55,basis7_55,basis8_55,basis9_55,basis10_55,basis11_55,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell55_0
theorem initial55_1 : JFn_PendingHistory.sum 55 ⟨1,by decide⟩=40523232 := by rfl
#print axioms initial55_1
theorem cell55_1 : JGv_QueryRows.weights 12 55 ⟨1,by decide⟩=(1619123029 : F) := by
  simp only [JGv_QueryRows.weights,initial55_1,basis0_55,basis1_55,basis2_55,basis3_55,basis4_55,basis5_55,basis6_55,basis7_55,basis8_55,basis9_55,basis10_55,basis11_55,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell55_1
theorem initial55_2 : JFn_PendingHistory.sum 55 ⟨2,by decide⟩=503071546 := by rfl
#print axioms initial55_2
theorem cell55_2 : JGv_QueryRows.weights 12 55 ⟨2,by decide⟩=(676070873 : F) := by
  simp only [JGv_QueryRows.weights,initial55_2,basis0_55,basis1_55,basis2_55,basis3_55,basis4_55,basis5_55,basis6_55,basis7_55,basis8_55,basis9_55,basis10_55,basis11_55,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell55_2
theorem initial55_3 : JFn_PendingHistory.sum 55 ⟨3,by decide⟩=1735787385 := by rfl
#print axioms initial55_3
theorem cell55_3 : JGv_QueryRows.weights 12 55 ⟨3,by decide⟩=(270487977 : F) := by
  simp only [JGv_QueryRows.weights,initial55_3,basis0_55,basis1_55,basis2_55,basis3_55,basis4_55,basis5_55,basis6_55,basis7_55,basis8_55,basis9_55,basis10_55,basis11_55,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell55_3
end AspisR1.JGv_WeightCells13
end
