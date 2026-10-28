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
namespace AspisR1.JGv_WeightCells02
open Aeneas Aeneas.Std
abbrev F := JGv_QueryRows.F
theorem basis0_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 8=(701318475 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor3,JGv_BasisFactors0.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_8
theorem basis1_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 8=(1662842815 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor3,JGv_BasisFactors1.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_8
theorem basis2_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 8=(1592782374 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor3,JGv_BasisFactors2.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_8
theorem basis3_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 8=(875908489 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor3,JGv_BasisFactors3.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_8
theorem basis4_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 8=(666918657 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor3,JGv_BasisFactors4.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_8
theorem basis5_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 8=(1213391976 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor3,JGv_BasisFactors5.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_8
theorem basis6_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 8=(2026942793 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor3,JGv_BasisFactors6.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_8
theorem basis7_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 8=(1458473586 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor3,JGv_BasisFactors7.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_8
theorem basis8_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 8=(825395511 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor3,JGv_BasisFactors8.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_8
theorem basis9_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 8=(761680311 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor3,JGv_BasisFactors9.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_8
theorem basis10_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 8=(25708084 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor3,JGv_BasisFactors10.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_8
theorem basis11_8 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 8=(2089182928 : F) := by
  change (∏ bit ∈ ({3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor3,JGv_BasisFactors11.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_8
theorem initial8_0 : JFn_PendingHistory.sum 8 ⟨0,by decide⟩=389252019 := by rfl
#print axioms initial8_0
theorem cell8_0 : JGv_QueryRows.weights 12 8 ⟨0,by decide⟩=(1986738822 : F) := by
  simp only [JGv_QueryRows.weights,initial8_0,basis0_8,basis1_8,basis2_8,basis3_8,basis4_8,basis5_8,basis6_8,basis7_8,basis8_8,basis9_8,basis10_8,basis11_8,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell8_0
theorem initial8_1 : JFn_PendingHistory.sum 8 ⟨1,by decide⟩=1335095117 := by rfl
#print axioms initial8_1
theorem cell8_1 : JGv_QueryRows.weights 12 8 ⟨1,by decide⟩=(719424318 : F) := by
  simp only [JGv_QueryRows.weights,initial8_1,basis0_8,basis1_8,basis2_8,basis3_8,basis4_8,basis5_8,basis6_8,basis7_8,basis8_8,basis9_8,basis10_8,basis11_8,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell8_1
theorem initial8_2 : JFn_PendingHistory.sum 8 ⟨2,by decide⟩=699564237 := by rfl
#print axioms initial8_2
theorem cell8_2 : JGv_QueryRows.weights 12 8 ⟨2,by decide⟩=(1343859011 : F) := by
  simp only [JGv_QueryRows.weights,initial8_2,basis0_8,basis1_8,basis2_8,basis3_8,basis4_8,basis5_8,basis6_8,basis7_8,basis8_8,basis9_8,basis10_8,basis11_8,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell8_2
theorem initial8_3 : JFn_PendingHistory.sum 8 ⟨3,by decide⟩=1326781228 := by rfl
#print axioms initial8_3
theorem cell8_3 : JGv_QueryRows.weights 12 8 ⟨3,by decide⟩=(2058267864 : F) := by
  simp only [JGv_QueryRows.weights,initial8_3,basis0_8,basis1_8,basis2_8,basis3_8,basis4_8,basis5_8,basis6_8,basis7_8,basis8_8,basis9_8,basis10_8,basis11_8,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell8_3
theorem basis0_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 9=(1476350135 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor3,JGv_BasisFactors0.x0,JGv_BasisFactors0.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_9
theorem basis1_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 9=(1103734462 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor3,JGv_BasisFactors1.x0,JGv_BasisFactors1.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_9
theorem basis2_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 9=(1073689887 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor3,JGv_BasisFactors2.x0,JGv_BasisFactors2.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_9
theorem basis3_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 9=(1095260569 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor3,JGv_BasisFactors3.x0,JGv_BasisFactors3.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_9
theorem basis4_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 9=(578519169 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor3,JGv_BasisFactors4.x0,JGv_BasisFactors4.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_9
theorem basis5_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 9=(785984018 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor3,JGv_BasisFactors5.x0,JGv_BasisFactors5.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_9
theorem basis6_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 9=(288676315 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor3,JGv_BasisFactors6.x0,JGv_BasisFactors6.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_9
theorem basis7_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 9=(542570792 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor3,JGv_BasisFactors7.x0,JGv_BasisFactors7.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_9
theorem basis8_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 9=(894534870 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor3,JGv_BasisFactors8.x0,JGv_BasisFactors8.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_9
theorem basis9_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 9=(655550412 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor3,JGv_BasisFactors9.x0,JGv_BasisFactors9.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_9
theorem basis10_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 9=(642141500 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor3,JGv_BasisFactors10.x0,JGv_BasisFactors10.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_9
theorem basis11_9 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 9=(238787173 : F) := by
  change (∏ bit ∈ ({0,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor3,JGv_BasisFactors11.x0,JGv_BasisFactors11.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_9
theorem initial9_0 : JFn_PendingHistory.sum 9 ⟨0,by decide⟩=1544585942 := by rfl
#print axioms initial9_0
theorem cell9_0 : JGv_QueryRows.weights 12 9 ⟨0,by decide⟩=(275173759 : F) := by
  simp only [JGv_QueryRows.weights,initial9_0,basis0_9,basis1_9,basis2_9,basis3_9,basis4_9,basis5_9,basis6_9,basis7_9,basis8_9,basis9_9,basis10_9,basis11_9,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell9_0
theorem initial9_1 : JFn_PendingHistory.sum 9 ⟨1,by decide⟩=164414659 := by rfl
#print axioms initial9_1
theorem cell9_1 : JGv_QueryRows.weights 12 9 ⟨1,by decide⟩=(1267159363 : F) := by
  simp only [JGv_QueryRows.weights,initial9_1,basis0_9,basis1_9,basis2_9,basis3_9,basis4_9,basis5_9,basis6_9,basis7_9,basis8_9,basis9_9,basis10_9,basis11_9,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell9_1
theorem initial9_2 : JFn_PendingHistory.sum 9 ⟨2,by decide⟩=1447575431 := by rfl
#print axioms initial9_2
theorem cell9_2 : JGv_QueryRows.weights 12 9 ⟨2,by decide⟩=(1013437998 : F) := by
  simp only [JGv_QueryRows.weights,initial9_2,basis0_9,basis1_9,basis2_9,basis3_9,basis4_9,basis5_9,basis6_9,basis7_9,basis8_9,basis9_9,basis10_9,basis11_9,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell9_2
theorem initial9_3 : JFn_PendingHistory.sum 9 ⟨3,by decide⟩=1037421148 := by rfl
#print axioms initial9_3
theorem cell9_3 : JGv_QueryRows.weights 12 9 ⟨3,by decide⟩=(889179630 : F) := by
  simp only [JGv_QueryRows.weights,initial9_3,basis0_9,basis1_9,basis2_9,basis3_9,basis4_9,basis5_9,basis6_9,basis7_9,basis8_9,basis9_9,basis10_9,basis11_9,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell9_3
theorem basis0_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 10=(1024271042 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor3,JGv_BasisFactors0.x1,JGv_BasisFactors0.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_10
theorem basis1_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 10=(731289684 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor3,JGv_BasisFactors1.x1,JGv_BasisFactors1.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_10
theorem basis2_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 10=(819481032 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor3,JGv_BasisFactors2.x1,JGv_BasisFactors2.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_10
theorem basis3_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 10=(637975755 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor3,JGv_BasisFactors3.x1,JGv_BasisFactors3.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_10
theorem basis4_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 10=(1944072181 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor3,JGv_BasisFactors4.x1,JGv_BasisFactors4.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_10
theorem basis5_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 10=(1044666345 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor3,JGv_BasisFactors5.x1,JGv_BasisFactors5.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_10
theorem basis6_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 10=(5122580 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor3,JGv_BasisFactors6.x1,JGv_BasisFactors6.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_10
theorem basis7_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 10=(1327951656 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor3,JGv_BasisFactors7.x1,JGv_BasisFactors7.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_10
theorem basis8_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 10=(1601688851 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor3,JGv_BasisFactors8.x1,JGv_BasisFactors8.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_10
theorem basis9_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 10=(1593948680 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor3,JGv_BasisFactors9.x1,JGv_BasisFactors9.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_10
theorem basis10_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 10=(2017484176 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor3,JGv_BasisFactors10.x1,JGv_BasisFactors10.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_10
theorem basis11_10 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 10=(9500019 : F) := by
  change (∏ bit ∈ ({1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor3,JGv_BasisFactors11.x1,JGv_BasisFactors11.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_10
theorem initial10_0 : JFn_PendingHistory.sum 10 ⟨0,by decide⟩=2007177445 := by rfl
#print axioms initial10_0
theorem cell10_0 : JGv_QueryRows.weights 12 10 ⟨0,by decide⟩=(1295531051 : F) := by
  simp only [JGv_QueryRows.weights,initial10_0,basis0_10,basis1_10,basis2_10,basis3_10,basis4_10,basis5_10,basis6_10,basis7_10,basis8_10,basis9_10,basis10_10,basis11_10,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell10_0
theorem initial10_1 : JFn_PendingHistory.sum 10 ⟨1,by decide⟩=1478027531 := by rfl
#print axioms initial10_1
theorem cell10_1 : JGv_QueryRows.weights 12 10 ⟨1,by decide⟩=(444805797 : F) := by
  simp only [JGv_QueryRows.weights,initial10_1,basis0_10,basis1_10,basis2_10,basis3_10,basis4_10,basis5_10,basis6_10,basis7_10,basis8_10,basis9_10,basis10_10,basis11_10,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell10_1
theorem initial10_2 : JFn_PendingHistory.sum 10 ⟨2,by decide⟩=543403815 := by rfl
#print axioms initial10_2
theorem cell10_2 : JGv_QueryRows.weights 12 10 ⟨2,by decide⟩=(2043538308 : F) := by
  simp only [JGv_QueryRows.weights,initial10_2,basis0_10,basis1_10,basis2_10,basis3_10,basis4_10,basis5_10,basis6_10,basis7_10,basis8_10,basis9_10,basis10_10,basis11_10,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell10_2
theorem initial10_3 : JFn_PendingHistory.sum 10 ⟨3,by decide⟩=1241504852 := by rfl
#print axioms initial10_3
theorem cell10_3 : JGv_QueryRows.weights 12 10 ⟨3,by decide⟩=(1391997703 : F) := by
  simp only [JGv_QueryRows.weights,initial10_3,basis0_10,basis1_10,basis2_10,basis3_10,basis4_10,basis5_10,basis6_10,basis7_10,basis8_10,basis9_10,basis10_10,basis11_10,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell10_3
theorem basis0_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) 11=(1265313390 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 0))) bit)=_
  norm_num [JGv_BasisFactors0.factor0,JGv_BasisFactors0.factor1,JGv_BasisFactors0.factor3,JGv_BasisFactors0.x0,JGv_BasisFactors0.x1,JGv_BasisFactors0.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis0_11
theorem basis1_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) 11=(626506656 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 1))) bit)=_
  norm_num [JGv_BasisFactors1.factor0,JGv_BasisFactors1.factor1,JGv_BasisFactors1.factor3,JGv_BasisFactors1.x0,JGv_BasisFactors1.x1,JGv_BasisFactors1.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis1_11
theorem basis2_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) 11=(581379070 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 2))) bit)=_
  norm_num [JGv_BasisFactors2.factor0,JGv_BasisFactors2.factor1,JGv_BasisFactors2.factor3,JGv_BasisFactors2.x0,JGv_BasisFactors2.x1,JGv_BasisFactors2.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis2_11
theorem basis3_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) 11=(1039764068 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 3))) bit)=_
  norm_num [JGv_BasisFactors3.factor0,JGv_BasisFactors3.factor1,JGv_BasisFactors3.factor3,JGv_BasisFactors3.x0,JGv_BasisFactors3.x1,JGv_BasisFactors3.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis3_11
theorem basis4_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) 11=(2137206003 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 4))) bit)=_
  norm_num [JGv_BasisFactors4.factor0,JGv_BasisFactors4.factor1,JGv_BasisFactors4.factor3,JGv_BasisFactors4.x0,JGv_BasisFactors4.x1,JGv_BasisFactors4.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis4_11
theorem basis5_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) 11=(1273979383 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 5))) bit)=_
  norm_num [JGv_BasisFactors5.factor0,JGv_BasisFactors5.factor1,JGv_BasisFactors5.factor3,JGv_BasisFactors5.x0,JGv_BasisFactors5.x1,JGv_BasisFactors5.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis5_11
theorem basis6_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) 11=(187396982 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 6))) bit)=_
  norm_num [JGv_BasisFactors6.factor0,JGv_BasisFactors6.factor1,JGv_BasisFactors6.factor3,JGv_BasisFactors6.x0,JGv_BasisFactors6.x1,JGv_BasisFactors6.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis6_11
theorem basis7_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) 11=(524576088 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 7))) bit)=_
  norm_num [JGv_BasisFactors7.factor0,JGv_BasisFactors7.factor1,JGv_BasisFactors7.factor3,JGv_BasisFactors7.x0,JGv_BasisFactors7.x1,JGv_BasisFactors7.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis7_11
theorem basis8_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) 11=(283447547 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 8))) bit)=_
  norm_num [JGv_BasisFactors8.factor0,JGv_BasisFactors8.factor1,JGv_BasisFactors8.factor3,JGv_BasisFactors8.x0,JGv_BasisFactors8.x1,JGv_BasisFactors8.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis8_11
theorem basis9_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) 11=(654590972 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 9))) bit)=_
  norm_num [JGv_BasisFactors9.factor0,JGv_BasisFactors9.factor1,JGv_BasisFactors9.factor3,JGv_BasisFactors9.x0,JGv_BasisFactors9.x1,JGv_BasisFactors9.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis9_11
theorem basis10_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) 11=(1084086540 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 10))) bit)=_
  norm_num [JGv_BasisFactors10.factor0,JGv_BasisFactors10.factor1,JGv_BasisFactors10.factor3,JGv_BasisFactors10.x0,JGv_BasisFactors10.x1,JGv_BasisFactors10.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis10_11
theorem basis11_11 : AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) 11=(1515357620 : F) := by
  change (∏ bit ∈ ({0,1,3} : Finset Nat),AspisCircleTensorBinding.doubledFactor (S7JoinBasisMachine.decode (JFz_TX2_Nodes.value (JFz_TX2_ChainStep.query 11))) bit)=_
  norm_num [JGv_BasisFactors11.factor0,JGv_BasisFactors11.factor1,JGv_BasisFactors11.factor3,JGv_BasisFactors11.x0,JGv_BasisFactors11.x1,JGv_BasisFactors11.x3]
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms basis11_11
theorem initial11_0 : JFn_PendingHistory.sum 11 ⟨0,by decide⟩=1733269172 := by rfl
#print axioms initial11_0
theorem cell11_0 : JGv_QueryRows.weights 12 11 ⟨0,by decide⟩=(1042112625 : F) := by
  simp only [JGv_QueryRows.weights,initial11_0,basis0_11,basis1_11,basis2_11,basis3_11,basis4_11,basis5_11,basis6_11,basis7_11,basis8_11,basis9_11,basis10_11,basis11_11,JGv_PowerLimbs.p0_0,JGv_PowerLimbs.p1_0,JGv_PowerLimbs.p2_0,JGv_PowerLimbs.p3_0,JGv_PowerLimbs.p4_0,JGv_PowerLimbs.p5_0,JGv_PowerLimbs.p6_0,JGv_PowerLimbs.p7_0,JGv_PowerLimbs.p8_0,JGv_PowerLimbs.p9_0,JGv_PowerLimbs.p10_0,JGv_PowerLimbs.p11_0]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell11_0
theorem initial11_1 : JFn_PendingHistory.sum 11 ⟨1,by decide⟩=517960228 := by rfl
#print axioms initial11_1
theorem cell11_1 : JGv_QueryRows.weights 12 11 ⟨1,by decide⟩=(1908496705 : F) := by
  simp only [JGv_QueryRows.weights,initial11_1,basis0_11,basis1_11,basis2_11,basis3_11,basis4_11,basis5_11,basis6_11,basis7_11,basis8_11,basis9_11,basis10_11,basis11_11,JGv_PowerLimbs.p0_1,JGv_PowerLimbs.p1_1,JGv_PowerLimbs.p2_1,JGv_PowerLimbs.p3_1,JGv_PowerLimbs.p4_1,JGv_PowerLimbs.p5_1,JGv_PowerLimbs.p6_1,JGv_PowerLimbs.p7_1,JGv_PowerLimbs.p8_1,JGv_PowerLimbs.p9_1,JGv_PowerLimbs.p10_1,JGv_PowerLimbs.p11_1]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell11_1
theorem initial11_2 : JFn_PendingHistory.sum 11 ⟨2,by decide⟩=187618203 := by rfl
#print axioms initial11_2
theorem cell11_2 : JGv_QueryRows.weights 12 11 ⟨2,by decide⟩=(1588146171 : F) := by
  simp only [JGv_QueryRows.weights,initial11_2,basis0_11,basis1_11,basis2_11,basis3_11,basis4_11,basis5_11,basis6_11,basis7_11,basis8_11,basis9_11,basis10_11,basis11_11,JGv_PowerLimbs.p0_2,JGv_PowerLimbs.p1_2,JGv_PowerLimbs.p2_2,JGv_PowerLimbs.p3_2,JGv_PowerLimbs.p4_2,JGv_PowerLimbs.p5_2,JGv_PowerLimbs.p6_2,JGv_PowerLimbs.p7_2,JGv_PowerLimbs.p8_2,JGv_PowerLimbs.p9_2,JGv_PowerLimbs.p10_2,JGv_PowerLimbs.p11_2]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell11_2
theorem initial11_3 : JFn_PendingHistory.sum 11 ⟨3,by decide⟩=1733556446 := by rfl
#print axioms initial11_3
theorem cell11_3 : JGv_QueryRows.weights 12 11 ⟨3,by decide⟩=(1741886415 : F) := by
  simp only [JGv_QueryRows.weights,initial11_3,basis0_11,basis1_11,basis2_11,basis3_11,basis4_11,basis5_11,basis6_11,basis7_11,basis8_11,basis9_11,basis10_11,basis11_11,JGv_PowerLimbs.p0_3,JGv_PowerLimbs.p1_3,JGv_PowerLimbs.p2_3,JGv_PowerLimbs.p3_3,JGv_PowerLimbs.p4_3,JGv_PowerLimbs.p5_3,JGv_PowerLimbs.p6_3,JGv_PowerLimbs.p7_3,JGv_PowerLimbs.p8_3,JGv_PowerLimbs.p9_3,JGv_PowerLimbs.p10_3,JGv_PowerLimbs.p11_3]
  norm_num
  all_goals apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  all_goals norm_num
#print axioms cell11_3
end AspisR1.JGv_WeightCells02
end
