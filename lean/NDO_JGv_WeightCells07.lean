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
namespace AspisR1.JGv_WeightCells07
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 28=(1349735512 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_28
theorem basis1_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 28=(1189955007 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_28
theorem basis2_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 28=(1605854581 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_28
theorem basis3_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 28=(1721986644 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_28
theorem basis4_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 28=(1534173435 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_28
theorem basis5_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 28=(1870814882 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_28
theorem basis6_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 28=(1805102984 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_28
theorem basis7_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 28=(47163396 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_28
theorem basis8_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 28=(2037241079 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_28
theorem basis9_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 28=(1025061580 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_28
theorem basis10_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 28=(83235376 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_28
theorem basis11_28 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 28=(1029571071 : F) := by
  change (∏ bit ∈ ({2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_28
theorem initial28_0 : JFn_PendingHistory.sum 28 ⟨0,by decide⟩=1284685638 := by rfl
#print axioms initial28_0
theorem cell28_0 : JGv_QueryRows.weights 12 28 ⟨0,by decide⟩=(1258951248 : F) := by
  simp only [JGv_QueryRows.weights,initial28_0,basis0_28,basis1_28,basis2_28,basis3_28,basis4_28,basis5_28,basis6_28,basis7_28,basis8_28,basis9_28,basis10_28,basis11_28,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell28_0
theorem initial28_1 : JFn_PendingHistory.sum 28 ⟨1,by decide⟩=1713701488 := by rfl
#print axioms initial28_1
theorem cell28_1 : JGv_QueryRows.weights 12 28 ⟨1,by decide⟩=(1310321396 : F) := by
  simp only [JGv_QueryRows.weights,initial28_1,basis0_28,basis1_28,basis2_28,basis3_28,basis4_28,basis5_28,basis6_28,basis7_28,basis8_28,basis9_28,basis10_28,basis11_28,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell28_1
theorem initial28_2 : JFn_PendingHistory.sum 28 ⟨2,by decide⟩=1196712103 := by rfl
#print axioms initial28_2
theorem cell28_2 : JGv_QueryRows.weights 12 28 ⟨2,by decide⟩=(1680101091 : F) := by
  simp only [JGv_QueryRows.weights,initial28_2,basis0_28,basis1_28,basis2_28,basis3_28,basis4_28,basis5_28,basis6_28,basis7_28,basis8_28,basis9_28,basis10_28,basis11_28,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell28_2
theorem initial28_3 : JFn_PendingHistory.sum 28 ⟨3,by decide⟩=673166315 := by rfl
#print axioms initial28_3
theorem cell28_3 : JGv_QueryRows.weights 12 28 ⟨3,by decide⟩=(173791872 : F) := by
  simp only [JGv_QueryRows.weights,initial28_3,basis0_28,basis1_28,basis2_28,basis3_28,basis4_28,basis5_28,basis6_28,basis7_28,basis8_28,basis9_28,basis10_28,basis11_28,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell28_3
theorem basis0_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 29=(691249293 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x0,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_29
theorem basis1_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 29=(691966210 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x0,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_29
theorem basis2_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 29=(1877399878 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x0,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_29
theorem basis3_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 29=(1257870938 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x0,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_29
theorem basis4_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 29=(1002713668 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x0,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_29
theorem basis5_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 29=(814694240 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x0,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_29
theorem basis6_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 29=(246088432 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x0,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_29
theorem basis7_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 29=(363151534 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x0,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_29
theorem basis8_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 29=(411975716 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x0,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_29
theorem basis9_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 29=(2051484221 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x0,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_29
theorem basis10_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 29=(836839145 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x0,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_29
theorem basis11_29 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 29=(1805337718 : F) := by
  change (∏ bit ∈ ({0,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x0,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_29
theorem initial29_0 : JFn_PendingHistory.sum 29 ⟨0,by decide⟩=1011626850 := by rfl
#print axioms initial29_0
theorem cell29_0 : JGv_QueryRows.weights 12 29 ⟨0,by decide⟩=(16150623 : F) := by
  simp only [JGv_QueryRows.weights,initial29_0,basis0_29,basis1_29,basis2_29,basis3_29,basis4_29,basis5_29,basis6_29,basis7_29,basis8_29,basis9_29,basis10_29,basis11_29,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell29_0
theorem initial29_1 : JFn_PendingHistory.sum 29 ⟨1,by decide⟩=1364074309 := by rfl
#print axioms initial29_1
theorem cell29_1 : JGv_QueryRows.weights 12 29 ⟨1,by decide⟩=(1141668881 : F) := by
  simp only [JGv_QueryRows.weights,initial29_1,basis0_29,basis1_29,basis2_29,basis3_29,basis4_29,basis5_29,basis6_29,basis7_29,basis8_29,basis9_29,basis10_29,basis11_29,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell29_1
theorem initial29_2 : JFn_PendingHistory.sum 29 ⟨2,by decide⟩=1911771696 := by rfl
#print axioms initial29_2
theorem cell29_2 : JGv_QueryRows.weights 12 29 ⟨2,by decide⟩=(1094622941 : F) := by
  simp only [JGv_QueryRows.weights,initial29_2,basis0_29,basis1_29,basis2_29,basis3_29,basis4_29,basis5_29,basis6_29,basis7_29,basis8_29,basis9_29,basis10_29,basis11_29,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell29_2
theorem initial29_3 : JFn_PendingHistory.sum 29 ⟨3,by decide⟩=242692980 := by rfl
#print axioms initial29_3
theorem cell29_3 : JGv_QueryRows.weights 12 29 ⟨3,by decide⟩=(655739894 : F) := by
  simp only [JGv_QueryRows.weights,initial29_3,basis0_29,basis1_29,basis2_29,basis3_29,basis4_29,basis5_29,basis6_29,basis7_29,basis8_29,basis9_29,basis10_29,basis11_29,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell29_3
theorem basis0_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 30=(45683026 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_30
theorem basis1_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 30=(334317112 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_30
theorem basis2_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 30=(1476908607 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_30
theorem basis3_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 30=(1715750543 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_30
theorem basis4_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 30=(1053099326 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_30
theorem basis5_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 30=(1104658127 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_30
theorem basis6_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 30=(58033356 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_30
theorem basis7_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 30=(390409622 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_30
theorem basis8_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 30=(674828270 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_30
theorem basis9_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 30=(635135156 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_30
theorem basis10_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 30=(1386090286 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_30
theorem basis11_30 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 30=(1700991230 : F) := by
  change (∏ bit ∈ ({1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_30
theorem initial30_0 : JFn_PendingHistory.sum 30 ⟨0,by decide⟩=1397827463 := by rfl
#print axioms initial30_0
theorem cell30_0 : JGv_QueryRows.weights 12 30 ⟨0,by decide⟩=(908041139 : F) := by
  simp only [JGv_QueryRows.weights,initial30_0,basis0_30,basis1_30,basis2_30,basis3_30,basis4_30,basis5_30,basis6_30,basis7_30,basis8_30,basis9_30,basis10_30,basis11_30,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell30_0
theorem initial30_1 : JFn_PendingHistory.sum 30 ⟨1,by decide⟩=2065720588 := by rfl
#print axioms initial30_1
theorem cell30_1 : JGv_QueryRows.weights 12 30 ⟨1,by decide⟩=(1770465907 : F) := by
  simp only [JGv_QueryRows.weights,initial30_1,basis0_30,basis1_30,basis2_30,basis3_30,basis4_30,basis5_30,basis6_30,basis7_30,basis8_30,basis9_30,basis10_30,basis11_30,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell30_1
theorem initial30_2 : JFn_PendingHistory.sum 30 ⟨2,by decide⟩=211843219 := by rfl
#print axioms initial30_2
theorem cell30_2 : JGv_QueryRows.weights 12 30 ⟨2,by decide⟩=(1674932710 : F) := by
  simp only [JGv_QueryRows.weights,initial30_2,basis0_30,basis1_30,basis2_30,basis3_30,basis4_30,basis5_30,basis6_30,basis7_30,basis8_30,basis9_30,basis10_30,basis11_30,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell30_2
theorem initial30_3 : JFn_PendingHistory.sum 30 ⟨3,by decide⟩=402797570 := by rfl
#print axioms initial30_3
theorem cell30_3 : JGv_QueryRows.weights 12 30 ⟨3,by decide⟩=(1823733702 : F) := by
  simp only [JGv_QueryRows.weights,initial30_3,basis0_30,basis1_30,basis2_30,basis3_30,basis4_30,basis5_30,basis6_30,basis7_30,basis8_30,basis9_30,basis10_30,basis11_30,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell30_3
theorem basis0_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 31=(655066523 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor2,JGv_BasisFactors0.factor3,JGv_BasisFactors0.factor4,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x2,JGv_BasisFactors0.x3,JGv_BasisFactors0.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_31
theorem basis1_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 31=(257880767 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor2,JGv_BasisFactors1.factor3,JGv_BasisFactors1.factor4,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x2,JGv_BasisFactors1.x3,JGv_BasisFactors1.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_31
theorem basis2_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 31=(838894812 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor2,JGv_BasisFactors2.factor3,JGv_BasisFactors2.factor4,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x2,JGv_BasisFactors2.x3,JGv_BasisFactors2.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_31
theorem basis3_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 31=(942543887 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor2,JGv_BasisFactors3.factor3,JGv_BasisFactors3.factor4,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x2,JGv_BasisFactors3.x3,JGv_BasisFactors3.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_31
theorem basis4_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 31=(1194875815 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor2,JGv_BasisFactors4.factor3,JGv_BasisFactors4.factor4,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x2,JGv_BasisFactors4.x3,JGv_BasisFactors4.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_31
theorem basis5_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 31=(1103117205 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor2,JGv_BasisFactors5.factor3,JGv_BasisFactors5.factor4,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x2,JGv_BasisFactors5.x3,JGv_BasisFactors5.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_31
theorem basis6_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 31=(8031785 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor2,JGv_BasisFactors6.factor3,JGv_BasisFactors6.factor4,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x2,JGv_BasisFactors6.x3,JGv_BasisFactors6.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_31
theorem basis7_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 31=(1880620446 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor2,JGv_BasisFactors7.factor3,JGv_BasisFactors7.factor4,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x2,JGv_BasisFactors7.x3,JGv_BasisFactors7.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_31
theorem basis8_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 31=(1800610895 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor2,JGv_BasisFactors8.factor3,JGv_BasisFactors8.factor4,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x2,JGv_BasisFactors8.x3,JGv_BasisFactors8.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_31
theorem basis9_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 31=(1119645381 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor2,JGv_BasisFactors9.factor3,JGv_BasisFactors9.factor4,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x2,JGv_BasisFactors9.x3,JGv_BasisFactors9.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_31
theorem basis10_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 31=(800844386 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor2,JGv_BasisFactors10.factor3,JGv_BasisFactors10.factor4,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x2,JGv_BasisFactors10.x3,JGv_BasisFactors10.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_31
theorem basis11_31 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 31=(1030502225 : F) := by
  change (∏ bit ∈ ({0,1,2,3,4} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor2,JGv_BasisFactors11.factor3,JGv_BasisFactors11.factor4,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x2,JGv_BasisFactors11.x3,JGv_BasisFactors11.x4]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_31
theorem initial31_0 : JFn_PendingHistory.sum 31 ⟨0,by decide⟩=1075414673 := by rfl
#print axioms initial31_0
theorem cell31_0 : JGv_QueryRows.weights 12 31 ⟨0,by decide⟩=(400434302 : F) := by
  simp only [JGv_QueryRows.weights,initial31_0,basis0_31,basis1_31,basis2_31,basis3_31,basis4_31,basis5_31,basis6_31,basis7_31,basis8_31,basis9_31,basis10_31,basis11_31,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell31_0
theorem initial31_1 : JFn_PendingHistory.sum 31 ⟨1,by decide⟩=300392344 := by rfl
#print axioms initial31_1
theorem cell31_1 : JGv_QueryRows.weights 12 31 ⟨1,by decide⟩=(2004558763 : F) := by
  simp only [JGv_QueryRows.weights,initial31_1,basis0_31,basis1_31,basis2_31,basis3_31,basis4_31,basis5_31,basis6_31,basis7_31,basis8_31,basis9_31,basis10_31,basis11_31,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell31_1
theorem initial31_2 : JFn_PendingHistory.sum 31 ⟨2,by decide⟩=1382562915 := by rfl
#print axioms initial31_2
theorem cell31_2 : JGv_QueryRows.weights 12 31 ⟨2,by decide⟩=(1173340669 : F) := by
  simp only [JGv_QueryRows.weights,initial31_2,basis0_31,basis1_31,basis2_31,basis3_31,basis4_31,basis5_31,basis6_31,basis7_31,basis8_31,basis9_31,basis10_31,basis11_31,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell31_2
theorem initial31_3 : JFn_PendingHistory.sum 31 ⟨3,by decide⟩=168039541 := by rfl
#print axioms initial31_3
theorem cell31_3 : JGv_QueryRows.weights 12 31 ⟨3,by decide⟩=(1520471559 : F) := by
  simp only [JGv_QueryRows.weights,initial31_3,basis0_31,basis1_31,basis2_31,basis3_31,basis4_31,basis5_31,basis6_31,basis7_31,basis8_31,basis9_31,basis10_31,basis11_31,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell31_3
end AspisR1.JGv_WeightCells07
end
