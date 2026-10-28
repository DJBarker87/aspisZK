import NDO_JHl_WeightFormula
import RPt_JFq_Weights08
import RPt_JFq_Weights09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight35_38
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis35_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 35=(1871228348 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis35_00

theorem basis35_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 35=(1993706132 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis35_01

theorem basis35_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 35=(252665178 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis35_02

theorem basis35_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 35=(2133534287 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis35_03

theorem basis35_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 35=(1601888356 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis35_04

theorem basis35_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 35=(1669268675 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis35_05

theorem basis35_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 35=(1944177067 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis35_06

theorem basis35_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 35=(1729030151 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis35_07

theorem basis35_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 35=(1577963553 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis35_08

theorem basis35_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 35=(47324214 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis35_09

theorem source35 : totalAt 10 35=CheckpointBytes5Output.ofK JFq_Weight35.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis35_00,basis35_01,basis35_02,basis35_03,basis35_04,basis35_05,basis35_06,basis35_07,basis35_08,basis35_09]
  change (0 : K)+ (1 : K)*scalar 1871228348+ JHk_Rhs00.power*scalar 1993706132+ JHk_Rhs01.power*scalar 252665178+ JHk_Rhs02.power*scalar 2133534287+ JHk_Rhs03.power*scalar 1601888356+ JHk_Rhs04.power*scalar 1669268675+ JHk_Rhs05.power*scalar 1944177067+ JHk_Rhs06.power*scalar 1729030151+ JHk_Rhs07.power*scalar 1577963553+ JHk_Rhs08.power*scalar 47324214=⟨⟨1152721183,445251663⟩,⟨1652054937,1074029892⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source35

theorem basis36_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 36=(403807127 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis36_00

theorem basis36_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 36=(1946304677 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis36_01

theorem basis36_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 36=(258718769 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis36_02

theorem basis36_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 36=(1268052595 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis36_03

theorem basis36_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 36=(558553808 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis36_04

theorem basis36_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 36=(1768833226 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis36_05

theorem basis36_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 36=(426676947 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis36_06

theorem basis36_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 36=(868834397 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis36_07

theorem basis36_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 36=(909211271 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis36_08

theorem basis36_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 36=(1367266460 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis36_09

theorem source36 : totalAt 10 36=CheckpointBytes5Output.ofK JFq_Weight36.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis36_00,basis36_01,basis36_02,basis36_03,basis36_04,basis36_05,basis36_06,basis36_07,basis36_08,basis36_09]
  change (0 : K)+ (1 : K)*scalar 403807127+ JHk_Rhs00.power*scalar 1946304677+ JHk_Rhs01.power*scalar 258718769+ JHk_Rhs02.power*scalar 1268052595+ JHk_Rhs03.power*scalar 558553808+ JHk_Rhs04.power*scalar 1768833226+ JHk_Rhs05.power*scalar 426676947+ JHk_Rhs06.power*scalar 868834397+ JHk_Rhs07.power*scalar 909211271+ JHk_Rhs08.power*scalar 1367266460=⟨⟨674614410,818789333⟩,⟨558783268,218318971⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source36

theorem basis37_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 37=(1067591335 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis37_00

theorem basis37_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 37=(570314342 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis37_01

theorem basis37_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 37=(791483164 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis37_02

theorem basis37_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 37=(2074831800 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis37_03

theorem basis37_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 37=(1968920497 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis37_04

theorem basis37_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 37=(1501462389 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis37_05

theorem basis37_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 37=(403022281 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis37_06

theorem basis37_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 37=(361979663 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis37_07

theorem basis37_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 37=(1539199610 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis37_08

theorem basis37_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 37=(864827590 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis37_09

theorem source37 : totalAt 10 37=CheckpointBytes5Output.ofK JFq_Weight37.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis37_00,basis37_01,basis37_02,basis37_03,basis37_04,basis37_05,basis37_06,basis37_07,basis37_08,basis37_09]
  change (0 : K)+ (1 : K)*scalar 1067591335+ JHk_Rhs00.power*scalar 570314342+ JHk_Rhs01.power*scalar 791483164+ JHk_Rhs02.power*scalar 2074831800+ JHk_Rhs03.power*scalar 1968920497+ JHk_Rhs04.power*scalar 1501462389+ JHk_Rhs05.power*scalar 403022281+ JHk_Rhs06.power*scalar 361979663+ JHk_Rhs07.power*scalar 1539199610+ JHk_Rhs08.power*scalar 864827590=⟨⟨1713979285,1438916743⟩,⟨1302357321,148287791⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source37

theorem basis38_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 38=(446362804 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis38_00

theorem basis38_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 38=(1362413139 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis38_01

theorem basis38_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 38=(1187055290 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis38_02

theorem basis38_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 38=(110080064 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis38_03

theorem basis38_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 38=(1060120249 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis38_04

theorem basis38_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 38=(1283293645 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis38_05

theorem basis38_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 38=(1021550575 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis38_06

theorem basis38_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 38=(378507906 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis38_07

theorem basis38_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 38=(943193698 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis38_08

theorem basis38_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 38=(1517069046 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis38_09

theorem source38 : totalAt 10 38=CheckpointBytes5Output.ofK JFq_Weight38.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis38_00,basis38_01,basis38_02,basis38_03,basis38_04,basis38_05,basis38_06,basis38_07,basis38_08,basis38_09]
  change (0 : K)+ (1 : K)*scalar 446362804+ JHk_Rhs00.power*scalar 1362413139+ JHk_Rhs01.power*scalar 1187055290+ JHk_Rhs02.power*scalar 110080064+ JHk_Rhs03.power*scalar 1060120249+ JHk_Rhs04.power*scalar 1283293645+ JHk_Rhs05.power*scalar 1021550575+ JHk_Rhs06.power*scalar 378507906+ JHk_Rhs07.power*scalar 943193698+ JHk_Rhs08.power*scalar 1517069046=⟨⟨185779811,1320962520⟩,⟨1505830063,1782657708⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source38
end AspisR1.JHl_Weight35_38
end
