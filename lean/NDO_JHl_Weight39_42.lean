import NDO_JHl_WeightFormula
import RPt_JFq_Weights09
import RPt_JFq_Weights10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight39_42
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis39_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 39=(516576642 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis39_00

theorem basis39_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 39=(2040068843 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis39_01

theorem basis39_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 39=(1409794354 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis39_02

theorem basis39_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 39=(1204315846 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis39_03

theorem basis39_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 39=(832880301 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis39_04

theorem basis39_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 39=(1265559105 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis39_05

theorem basis39_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 39=(1078239646 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis39_06

theorem basis39_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 39=(276451776 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis39_07

theorem basis39_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 39=(374893078 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis39_08

theorem basis39_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 39=(1539640938 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis39_09

theorem source39 : totalAt 10 39=CheckpointBytes5Output.ofK JFq_Weight39.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis39_00,basis39_01,basis39_02,basis39_03,basis39_04,basis39_05,basis39_06,basis39_07,basis39_08,basis39_09]
  change (0 : K)+ (1 : K)*scalar 516576642+ JHk_Rhs00.power*scalar 2040068843+ JHk_Rhs01.power*scalar 1409794354+ JHk_Rhs02.power*scalar 1204315846+ JHk_Rhs03.power*scalar 832880301+ JHk_Rhs04.power*scalar 1265559105+ JHk_Rhs05.power*scalar 1078239646+ JHk_Rhs06.power*scalar 276451776+ JHk_Rhs07.power*scalar 374893078+ JHk_Rhs08.power*scalar 1539640938=⟨⟨1507083850,2119799835⟩,⟨550793889,2086293603⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source39

theorem basis40_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 40=(1664861484 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis40_00

theorem basis40_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 40=(1054094146 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis40_01

theorem basis40_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 40=(1469590999 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis40_02

theorem basis40_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 40=(1861318930 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis40_03

theorem basis40_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 40=(1983314416 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis40_04

theorem basis40_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 40=(694145288 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis40_05

theorem basis40_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 40=(303892554 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis40_06

theorem basis40_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 40=(1807290751 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis40_07

theorem basis40_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 40=(1540145839 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis40_08

theorem basis40_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 40=(1413992874 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis40_09

theorem source40 : totalAt 10 40=CheckpointBytes5Output.ofK JFq_Weight40.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis40_00,basis40_01,basis40_02,basis40_03,basis40_04,basis40_05,basis40_06,basis40_07,basis40_08,basis40_09]
  change (0 : K)+ (1 : K)*scalar 1664861484+ JHk_Rhs00.power*scalar 1054094146+ JHk_Rhs01.power*scalar 1469590999+ JHk_Rhs02.power*scalar 1861318930+ JHk_Rhs03.power*scalar 1983314416+ JHk_Rhs04.power*scalar 694145288+ JHk_Rhs05.power*scalar 303892554+ JHk_Rhs06.power*scalar 1807290751+ JHk_Rhs07.power*scalar 1540145839+ JHk_Rhs08.power*scalar 1413992874=⟨⟨509611174,1233335108⟩,⟨1623479275,856336094⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source40

theorem basis41_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 41=(664361240 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis41_00

theorem basis41_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 41=(1855158621 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis41_01

theorem basis41_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 41=(1630358592 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis41_02

theorem basis41_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 41=(1082329679 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis41_03

theorem basis41_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 41=(1834367559 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis41_04

theorem basis41_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 41=(1444865860 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis41_05

theorem basis41_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 41=(807397366 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis41_06

theorem basis41_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 41=(910293604 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis41_07

theorem basis41_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 41=(874540434 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis41_08

theorem basis41_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 41=(625584769 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis41_09

theorem source41 : totalAt 10 41=CheckpointBytes5Output.ofK JFq_Weight41.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis41_00,basis41_01,basis41_02,basis41_03,basis41_04,basis41_05,basis41_06,basis41_07,basis41_08,basis41_09]
  change (0 : K)+ (1 : K)*scalar 664361240+ JHk_Rhs00.power*scalar 1855158621+ JHk_Rhs01.power*scalar 1630358592+ JHk_Rhs02.power*scalar 1082329679+ JHk_Rhs03.power*scalar 1834367559+ JHk_Rhs04.power*scalar 1444865860+ JHk_Rhs05.power*scalar 807397366+ JHk_Rhs06.power*scalar 910293604+ JHk_Rhs07.power*scalar 874540434+ JHk_Rhs08.power*scalar 625584769=⟨⟨1727338470,2110902286⟩,⟨2141221734,1098319118⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source41

theorem basis42_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 42=(992471475 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis42_00

theorem basis42_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 42=(90911483 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis42_01

theorem basis42_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 42=(349759687 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis42_02

theorem basis42_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 42=(165020429 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis42_03

theorem basis42_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 42=(1004315623 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis42_04

theorem basis42_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 42=(1123425917 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis42_05

theorem basis42_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 42=(218054237 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis42_06

theorem basis42_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 42=(847752092 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis42_07

theorem basis42_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 42=(929116655 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis42_08

theorem basis42_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 42=(71994838 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis42_09

theorem source42 : totalAt 10 42=CheckpointBytes5Output.ofK JFq_Weight42.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis42_00,basis42_01,basis42_02,basis42_03,basis42_04,basis42_05,basis42_06,basis42_07,basis42_08,basis42_09]
  change (0 : K)+ (1 : K)*scalar 992471475+ JHk_Rhs00.power*scalar 90911483+ JHk_Rhs01.power*scalar 349759687+ JHk_Rhs02.power*scalar 165020429+ JHk_Rhs03.power*scalar 1004315623+ JHk_Rhs04.power*scalar 1123425917+ JHk_Rhs05.power*scalar 218054237+ JHk_Rhs06.power*scalar 847752092+ JHk_Rhs07.power*scalar 929116655+ JHk_Rhs08.power*scalar 71994838=⟨⟨766839081,1942075625⟩,⟨144752729,1362812189⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source42
end AspisR1.JHl_Weight39_42
end
