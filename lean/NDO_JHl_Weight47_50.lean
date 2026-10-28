import NDO_JHl_WeightFormula
import RPt_JFq_Weights11
import RPt_JFq_Weights12
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight47_50
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis47_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 47=(900892205 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis47_00

theorem basis47_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 47=(1572337515 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis47_01

theorem basis47_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 47=(634822846 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis47_02

theorem basis47_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 47=(1155263020 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis47_03

theorem basis47_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 47=(1433773184 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis47_04

theorem basis47_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 47=(1694520132 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis47_05

theorem basis47_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 47=(1050317137 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis47_06

theorem basis47_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 47=(840112040 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis47_07

theorem basis47_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 47=(578476286 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis47_08

theorem basis47_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 47=(26383617 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis47_09

theorem source47 : totalAt 10 47=CheckpointBytes5Output.ofK JFq_Weight47.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis47_00,basis47_01,basis47_02,basis47_03,basis47_04,basis47_05,basis47_06,basis47_07,basis47_08,basis47_09]
  change (0 : K)+ (1 : K)*scalar 900892205+ JHk_Rhs00.power*scalar 1572337515+ JHk_Rhs01.power*scalar 634822846+ JHk_Rhs02.power*scalar 1155263020+ JHk_Rhs03.power*scalar 1433773184+ JHk_Rhs04.power*scalar 1694520132+ JHk_Rhs05.power*scalar 1050317137+ JHk_Rhs06.power*scalar 840112040+ JHk_Rhs07.power*scalar 578476286+ JHk_Rhs08.power*scalar 26383617=⟨⟨1771947506,1221379243⟩,⟨2025482235,1499321063⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source47

theorem basis48_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 48=(949405777 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis48_00

theorem basis48_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 48=(2107474741 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis48_01

theorem basis48_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 48=(1920358892 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis48_02

theorem basis48_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 48=(278298424 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis48_03

theorem basis48_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 48=(1107615299 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis48_04

theorem basis48_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 48=(1319257478 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis48_05

theorem basis48_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 48=(114903514 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis48_06

theorem basis48_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 48=(183439386 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis48_07

theorem basis48_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 48=(1246869080 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis48_08

theorem basis48_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 48=(1871385052 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis48_09

theorem source48 : totalAt 10 48=CheckpointBytes5Output.ofK JFq_Weight48.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis48_00,basis48_01,basis48_02,basis48_03,basis48_04,basis48_05,basis48_06,basis48_07,basis48_08,basis48_09]
  change (0 : K)+ (1 : K)*scalar 949405777+ JHk_Rhs00.power*scalar 2107474741+ JHk_Rhs01.power*scalar 1920358892+ JHk_Rhs02.power*scalar 278298424+ JHk_Rhs03.power*scalar 1107615299+ JHk_Rhs04.power*scalar 1319257478+ JHk_Rhs05.power*scalar 114903514+ JHk_Rhs06.power*scalar 183439386+ JHk_Rhs07.power*scalar 1246869080+ JHk_Rhs08.power*scalar 1871385052=⟨⟨172803113,1364024569⟩,⟨1496042614,78290953⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source48

theorem basis49_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 49=(1775542349 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis49_00

theorem basis49_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 49=(1567314471 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis49_01

theorem basis49_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 49=(2002724102 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis49_02

theorem basis49_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 49=(2039023798 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis49_03

theorem basis49_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 49=(1507611184 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis49_04

theorem basis49_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 49=(637890142 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis49_05

theorem basis49_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 49=(1994123941 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis49_06

theorem basis49_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 49=(1421468850 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis49_07

theorem basis49_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 49=(1263219119 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis49_08

theorem basis49_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 49=(1899524430 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis49_09

theorem source49 : totalAt 10 49=CheckpointBytes5Output.ofK JFq_Weight49.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis49_00,basis49_01,basis49_02,basis49_03,basis49_04,basis49_05,basis49_06,basis49_07,basis49_08,basis49_09]
  change (0 : K)+ (1 : K)*scalar 1775542349+ JHk_Rhs00.power*scalar 1567314471+ JHk_Rhs01.power*scalar 2002724102+ JHk_Rhs02.power*scalar 2039023798+ JHk_Rhs03.power*scalar 1507611184+ JHk_Rhs04.power*scalar 637890142+ JHk_Rhs05.power*scalar 1994123941+ JHk_Rhs06.power*scalar 1421468850+ JHk_Rhs07.power*scalar 1263219119+ JHk_Rhs08.power*scalar 1899524430=⟨⟨2081583345,1978401330⟩,⟨227089229,1219742090⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source49

theorem basis50_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 50=(1124379807 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis50_00

theorem basis50_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 50=(1704786459 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis50_01

theorem basis50_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 50=(308798404 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis50_02

theorem basis50_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 50=(1886007232 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis50_03

theorem basis50_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 50=(824033291 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis50_04

theorem basis50_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 50=(1106094757 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis50_05

theorem basis50_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 50=(1828757337 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis50_06

theorem basis50_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 50=(1292244945 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis50_07

theorem basis50_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 50=(454414822 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis50_08

theorem basis50_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 50=(1952139654 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis50_09

theorem source50 : totalAt 10 50=CheckpointBytes5Output.ofK JFq_Weight50.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis50_00,basis50_01,basis50_02,basis50_03,basis50_04,basis50_05,basis50_06,basis50_07,basis50_08,basis50_09]
  change (0 : K)+ (1 : K)*scalar 1124379807+ JHk_Rhs00.power*scalar 1704786459+ JHk_Rhs01.power*scalar 308798404+ JHk_Rhs02.power*scalar 1886007232+ JHk_Rhs03.power*scalar 824033291+ JHk_Rhs04.power*scalar 1106094757+ JHk_Rhs05.power*scalar 1828757337+ JHk_Rhs06.power*scalar 1292244945+ JHk_Rhs07.power*scalar 454414822+ JHk_Rhs08.power*scalar 1952139654=⟨⟨1943312160,1988336833⟩,⟨1224041218,459994729⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source50
end AspisR1.JHl_Weight47_50
end
