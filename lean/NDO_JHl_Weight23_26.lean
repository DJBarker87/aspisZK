import NDO_JHl_WeightFormula
import RPt_JFq_Weights05
import RPt_JFq_Weights06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight23_26
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis23_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 23=(774826591 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis23_00

theorem basis23_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 23=(1036489799 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis23_01

theorem basis23_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 23=(920956626 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis23_02

theorem basis23_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 23=(665634724 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis23_03

theorem basis23_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 23=(895608296 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis23_04

theorem basis23_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 23=(1518802944 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis23_05

theorem basis23_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 23=(735941753 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis23_06

theorem basis23_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 23=(1512305730 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis23_07

theorem basis23_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 23=(1035430734 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis23_08

theorem basis23_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 23=(557916049 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis23_09

theorem source23 : totalAt 10 23=CheckpointBytes5Output.ofK JFq_Weight23.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis23_00,basis23_01,basis23_02,basis23_03,basis23_04,basis23_05,basis23_06,basis23_07,basis23_08,basis23_09]
  change (0 : K)+ (1 : K)*scalar 774826591+ JHk_Rhs00.power*scalar 1036489799+ JHk_Rhs01.power*scalar 920956626+ JHk_Rhs02.power*scalar 665634724+ JHk_Rhs03.power*scalar 895608296+ JHk_Rhs04.power*scalar 1518802944+ JHk_Rhs05.power*scalar 735941753+ JHk_Rhs06.power*scalar 1512305730+ JHk_Rhs07.power*scalar 1035430734+ JHk_Rhs08.power*scalar 557916049=⟨⟨1087467590,1167070157⟩,⟨218265742,768893347⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source23

theorem basis24_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 24=(250339746 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis24_00

theorem basis24_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 24=(451955745 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis24_01

theorem basis24_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 24=(1111778198 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis24_02

theorem basis24_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 24=(1929284041 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis24_03

theorem basis24_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 24=(154962761 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis24_04

theorem basis24_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 24=(1155850388 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis24_05

theorem basis24_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 24=(1179197153 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis24_06

theorem basis24_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 24=(1414335863 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis24_07

theorem basis24_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 24=(460134180 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis24_08

theorem basis24_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 24=(1853671870 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis24_09

theorem source24 : totalAt 10 24=CheckpointBytes5Output.ofK JFq_Weight24.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis24_00,basis24_01,basis24_02,basis24_03,basis24_04,basis24_05,basis24_06,basis24_07,basis24_08,basis24_09]
  change (0 : K)+ (1 : K)*scalar 250339746+ JHk_Rhs00.power*scalar 451955745+ JHk_Rhs01.power*scalar 1111778198+ JHk_Rhs02.power*scalar 1929284041+ JHk_Rhs03.power*scalar 154962761+ JHk_Rhs04.power*scalar 1155850388+ JHk_Rhs05.power*scalar 1179197153+ JHk_Rhs06.power*scalar 1414335863+ JHk_Rhs07.power*scalar 460134180+ JHk_Rhs08.power*scalar 1853671870=⟨⟨1938176182,878750579⟩,⟨464240492,370464749⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source24

theorem basis25_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 25=(976459789 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis25_00

theorem basis25_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 25=(141427290 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis25_01

theorem basis25_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 25=(1012554720 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis25_02

theorem basis25_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 25=(2144440652 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis25_03

theorem basis25_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 25=(695841784 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis25_04

theorem basis25_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 25=(500762376 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis25_05

theorem basis25_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 25=(1658062048 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis25_06

theorem basis25_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 25=(1979910953 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis25_07

theorem basis25_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 25=(1392379257 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis25_08

theorem basis25_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 25=(413004568 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis25_09

theorem source25 : totalAt 10 25=CheckpointBytes5Output.ofK JFq_Weight25.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis25_00,basis25_01,basis25_02,basis25_03,basis25_04,basis25_05,basis25_06,basis25_07,basis25_08,basis25_09]
  change (0 : K)+ (1 : K)*scalar 976459789+ JHk_Rhs00.power*scalar 141427290+ JHk_Rhs01.power*scalar 1012554720+ JHk_Rhs02.power*scalar 2144440652+ JHk_Rhs03.power*scalar 695841784+ JHk_Rhs04.power*scalar 500762376+ JHk_Rhs05.power*scalar 1658062048+ JHk_Rhs06.power*scalar 1979910953+ JHk_Rhs07.power*scalar 1392379257+ JHk_Rhs08.power*scalar 413004568=⟨⟨1549429475,388897123⟩,⟨2078928895,614800989⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source25

theorem basis26_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 26=(671563135 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis26_00

theorem basis26_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 26=(1785553195 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis26_01

theorem basis26_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 26=(947134215 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis26_02

theorem basis26_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 26=(90076860 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis26_03

theorem basis26_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 26=(2052859271 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis26_04

theorem basis26_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 26=(1470032026 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis26_05

theorem basis26_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 26=(2023539331 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis26_06

theorem basis26_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 26=(1273629883 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis26_07

theorem basis26_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 26=(1908648390 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis26_08

theorem basis26_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 26=(968387974 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis26_09

theorem source26 : totalAt 10 26=CheckpointBytes5Output.ofK JFq_Weight26.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis26_00,basis26_01,basis26_02,basis26_03,basis26_04,basis26_05,basis26_06,basis26_07,basis26_08,basis26_09]
  change (0 : K)+ (1 : K)*scalar 671563135+ JHk_Rhs00.power*scalar 1785553195+ JHk_Rhs01.power*scalar 947134215+ JHk_Rhs02.power*scalar 90076860+ JHk_Rhs03.power*scalar 2052859271+ JHk_Rhs04.power*scalar 1470032026+ JHk_Rhs05.power*scalar 2023539331+ JHk_Rhs06.power*scalar 1273629883+ JHk_Rhs07.power*scalar 1908648390+ JHk_Rhs08.power*scalar 968387974=⟨⟨833455043,2045046271⟩,⟨868333983,1954240680⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source26
end AspisR1.JHl_Weight23_26
end
