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
namespace AspisR1.JGv_WeightCells09
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 36=(578282228 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x2,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_36
theorem basis1_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 36=(150967945 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x2,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_36
theorem basis2_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 36=(1355970036 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x2,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_36
theorem basis3_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 36=(898556283 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x2,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_36
theorem basis4_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 36=(499670453 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x2,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_36
theorem basis5_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 36=(1301303074 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x2,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_36
theorem basis6_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 36=(1643426226 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x2,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_36
theorem basis7_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 36=(2097620872 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x2,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_36
theorem basis8_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 36=(2006698369 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x2,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_36
theorem basis9_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 36=(222167109 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x2,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_36
theorem basis10_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 36=(1445194775 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x2,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_36
theorem basis11_36 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 36=(2083135736 : F) := by
  change (∏ bit ∈ ({2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x2,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_36
theorem initial36_0 : JFn_PendingHistory.sum 36 ⟨0,by decide⟩=674614410 := by rfl
#print axioms initial36_0
theorem cell36_0 : JGv_QueryRows.weights 12 36 ⟨0,by decide⟩=(1028259333 : F) := by
  simp only [JGv_QueryRows.weights,initial36_0,basis0_36,basis1_36,basis2_36,basis3_36,basis4_36,basis5_36,basis6_36,basis7_36,basis8_36,basis9_36,basis10_36,basis11_36,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell36_0
theorem initial36_1 : JFn_PendingHistory.sum 36 ⟨1,by decide⟩=818789333 := by rfl
#print axioms initial36_1
theorem cell36_1 : JGv_QueryRows.weights 12 36 ⟨1,by decide⟩=(507000493 : F) := by
  simp only [JGv_QueryRows.weights,initial36_1,basis0_36,basis1_36,basis2_36,basis3_36,basis4_36,basis5_36,basis6_36,basis7_36,basis8_36,basis9_36,basis10_36,basis11_36,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell36_1
theorem initial36_2 : JFn_PendingHistory.sum 36 ⟨2,by decide⟩=558783268 := by rfl
#print axioms initial36_2
theorem cell36_2 : JGv_QueryRows.weights 12 36 ⟨2,by decide⟩=(2025349103 : F) := by
  simp only [JGv_QueryRows.weights,initial36_2,basis0_36,basis1_36,basis2_36,basis3_36,basis4_36,basis5_36,basis6_36,basis7_36,basis8_36,basis9_36,basis10_36,basis11_36,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell36_2
theorem initial36_3 : JFn_PendingHistory.sum 36 ⟨3,by decide⟩=218318971 := by rfl
#print axioms initial36_3
theorem cell36_3 : JGv_QueryRows.weights 12 36 ⟨3,by decide⟩=(1434664328 : F) := by
  simp only [JGv_QueryRows.weights,initial36_3,basis0_36,basis1_36,basis2_36,basis3_36,basis4_36,basis5_36,basis6_36,basis7_36,basis8_36,basis9_36,basis10_36,basis11_36,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell36_3
theorem basis0_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 37=(1610162618 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x2,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_37
theorem basis1_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 37=(551865967 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x2,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_37
theorem basis2_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 37=(2123309064 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x2,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_37
theorem basis3_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 37=(2099021226 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x2,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_37
theorem basis4_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 37=(955625883 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x2,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_37
theorem basis5_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 37=(521109033 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x2,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_37
theorem basis6_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 37=(1032612737 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x2,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_37
theorem basis7_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 37=(626964112 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x2,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_37
theorem basis8_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 37=(170327028 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x2,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_37
theorem basis9_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 37=(434147086 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x2,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_37
theorem basis10_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 37=(1488102579 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x2,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_37
theorem basis11_37 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 37=(542067543 : F) := by
  change (∏ bit ∈ ({0,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x2,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_37
theorem initial37_0 : JFn_PendingHistory.sum 37 ⟨0,by decide⟩=1713979285 := by rfl
#print axioms initial37_0
theorem cell37_0 : JGv_QueryRows.weights 12 37 ⟨0,by decide⟩=(1448571246 : F) := by
  simp only [JGv_QueryRows.weights,initial37_0,basis0_37,basis1_37,basis2_37,basis3_37,basis4_37,basis5_37,basis6_37,basis7_37,basis8_37,basis9_37,basis10_37,basis11_37,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell37_0
theorem initial37_1 : JFn_PendingHistory.sum 37 ⟨1,by decide⟩=1438916743 := by rfl
#print axioms initial37_1
theorem cell37_1 : JGv_QueryRows.weights 12 37 ⟨1,by decide⟩=(1948866405 : F) := by
  simp only [JGv_QueryRows.weights,initial37_1,basis0_37,basis1_37,basis2_37,basis3_37,basis4_37,basis5_37,basis6_37,basis7_37,basis8_37,basis9_37,basis10_37,basis11_37,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell37_1
theorem initial37_2 : JFn_PendingHistory.sum 37 ⟨2,by decide⟩=1302357321 := by rfl
#print axioms initial37_2
theorem cell37_2 : JGv_QueryRows.weights 12 37 ⟨2,by decide⟩=(632540015 : F) := by
  simp only [JGv_QueryRows.weights,initial37_2,basis0_37,basis1_37,basis2_37,basis3_37,basis4_37,basis5_37,basis6_37,basis7_37,basis8_37,basis9_37,basis10_37,basis11_37,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell37_2
theorem initial37_3 : JFn_PendingHistory.sum 37 ⟨3,by decide⟩=148287791 := by rfl
#print axioms initial37_3
theorem cell37_3 : JGv_QueryRows.weights 12 37 ⟨3,by decide⟩=(229398289 : F) := by
  simp only [JGv_QueryRows.weights,initial37_3,basis0_37,basis1_37,basis2_37,basis3_37,basis4_37,basis5_37,basis6_37,basis7_37,basis8_37,basis9_37,basis10_37,basis11_37,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell37_3
theorem basis0_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 38=(16956754 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_38
theorem basis1_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 38=(166450754 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_38
theorem basis2_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 38=(1168468416 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_38
theorem basis3_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 38=(2021379672 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_38
theorem basis4_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 38=(1420203481 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_38
theorem basis5_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 38=(1315637344 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_38
theorem basis6_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 38=(1766284486 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_38
theorem basis7_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 38=(1158904772 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_38
theorem basis8_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 38=(969604130 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_38
theorem basis9_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 38=(1498492521 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_38
theorem basis10_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 38=(673039562 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_38
theorem basis11_38 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 38=(826677511 : F) := by
  change (∏ bit ∈ ({1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_38
theorem initial38_0 : JFn_PendingHistory.sum 38 ⟨0,by decide⟩=185779811 := by rfl
#print axioms initial38_0
theorem cell38_0 : JGv_QueryRows.weights 12 38 ⟨0,by decide⟩=(918308012 : F) := by
  simp only [JGv_QueryRows.weights,initial38_0,basis0_38,basis1_38,basis2_38,basis3_38,basis4_38,basis5_38,basis6_38,basis7_38,basis8_38,basis9_38,basis10_38,basis11_38,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell38_0
theorem initial38_1 : JFn_PendingHistory.sum 38 ⟨1,by decide⟩=1320962520 := by rfl
#print axioms initial38_1
theorem cell38_1 : JGv_QueryRows.weights 12 38 ⟨1,by decide⟩=(1513877604 : F) := by
  simp only [JGv_QueryRows.weights,initial38_1,basis0_38,basis1_38,basis2_38,basis3_38,basis4_38,basis5_38,basis6_38,basis7_38,basis8_38,basis9_38,basis10_38,basis11_38,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell38_1
theorem initial38_2 : JFn_PendingHistory.sum 38 ⟨2,by decide⟩=1505830063 := by rfl
#print axioms initial38_2
theorem cell38_2 : JGv_QueryRows.weights 12 38 ⟨2,by decide⟩=(841600172 : F) := by
  simp only [JGv_QueryRows.weights,initial38_2,basis0_38,basis1_38,basis2_38,basis3_38,basis4_38,basis5_38,basis6_38,basis7_38,basis8_38,basis9_38,basis10_38,basis11_38,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell38_2
theorem initial38_3 : JFn_PendingHistory.sum 38 ⟨3,by decide⟩=1782657708 := by rfl
#print axioms initial38_3
theorem cell38_3 : JGv_QueryRows.weights 12 38 ⟨3,by decide⟩=(2024779411 : F) := by
  simp only [JGv_QueryRows.weights,initial38_3,basis0_38,basis1_38,basis2_38,basis3_38,basis4_38,basis5_38,basis6_38,basis7_38,basis8_38,basis9_38,basis10_38,basis11_38,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell38_3
theorem basis0_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 39=(193934418 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor5,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_39
theorem basis1_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 39=(875372897 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor5,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_39
theorem basis2_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 39=(1016610530 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor5,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_39
theorem basis3_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 39=(191113685 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor5,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_39
theorem basis4_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 39=(306293711 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor5,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_39
theorem basis5_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 39=(658342641 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor5,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_39
theorem basis6_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 39=(1931579672 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor5,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_39
theorem basis7_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 39=(1107900994 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor5,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_39
theorem basis8_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 39=(1250213962 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor5,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_39
theorem basis9_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 39=(1999316853 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor5,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_39
theorem basis10_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 39=(177402252 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor5,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_39
theorem basis11_39 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 39=(1074393720 : F) := by
  change (∏ bit ∈ ({0,1,2,5} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor5,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x5]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_39
theorem initial39_0 : JFn_PendingHistory.sum 39 ⟨0,by decide⟩=1507083850 := by rfl
#print axioms initial39_0
theorem cell39_0 : JGv_QueryRows.weights 12 39 ⟨0,by decide⟩=(1980912663 : F) := by
  simp only [JGv_QueryRows.weights,initial39_0,basis0_39,basis1_39,basis2_39,basis3_39,basis4_39,basis5_39,basis6_39,basis7_39,basis8_39,basis9_39,basis10_39,basis11_39,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell39_0
theorem initial39_1 : JFn_PendingHistory.sum 39 ⟨1,by decide⟩=2119799835 := by rfl
#print axioms initial39_1
theorem cell39_1 : JGv_QueryRows.weights 12 39 ⟨1,by decide⟩=(2085812151 : F) := by
  simp only [JGv_QueryRows.weights,initial39_1,basis0_39,basis1_39,basis2_39,basis3_39,basis4_39,basis5_39,basis6_39,basis7_39,basis8_39,basis9_39,basis10_39,basis11_39,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell39_1
theorem initial39_2 : JFn_PendingHistory.sum 39 ⟨2,by decide⟩=550793889 := by rfl
#print axioms initial39_2
theorem cell39_2 : JGv_QueryRows.weights 12 39 ⟨2,by decide⟩=(331709984 : F) := by
  simp only [JGv_QueryRows.weights,initial39_2,basis0_39,basis1_39,basis2_39,basis3_39,basis4_39,basis5_39,basis6_39,basis7_39,basis8_39,basis9_39,basis10_39,basis11_39,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell39_2
theorem initial39_3 : JFn_PendingHistory.sum 39 ⟨3,by decide⟩=2086293603 := by rfl
#print axioms initial39_3
theorem cell39_3 : JGv_QueryRows.weights 12 39 ⟨3,by decide⟩=(172002647 : F) := by
  simp only [JGv_QueryRows.weights,initial39_3,basis0_39,basis1_39,basis2_39,basis3_39,basis4_39,basis5_39,basis6_39,basis7_39,basis8_39,basis9_39,basis10_39,basis11_39,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell39_3
end AspisR1.JGv_WeightCells09
end
