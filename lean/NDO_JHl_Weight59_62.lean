import NDO_JHl_WeightFormula
import RPt_JFq_Weights14
import RPt_JFq_Weights15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight59_62
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis59_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 59=(96774531 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis59_00

theorem basis59_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 59=(1114457163 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis59_01

theorem basis59_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 59=(1271822527 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis59_02

theorem basis59_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 59=(318942122 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis59_03

theorem basis59_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 59=(338957770 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis59_04

theorem basis59_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 59=(1758643221 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis59_05

theorem basis59_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 59=(1383659086 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis59_06

theorem basis59_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 59=(61933653 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis59_07

theorem basis59_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 59=(618155599 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis59_08

theorem basis59_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 59=(1890494031 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis59_09

theorem source59 : totalAt 10 59=CheckpointBytes5Output.ofK JFq_Weight59.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis59_00,basis59_01,basis59_02,basis59_03,basis59_04,basis59_05,basis59_06,basis59_07,basis59_08,basis59_09]
  change (0 : K)+ (1 : K)*scalar 96774531+ JHk_Rhs00.power*scalar 1114457163+ JHk_Rhs01.power*scalar 1271822527+ JHk_Rhs02.power*scalar 318942122+ JHk_Rhs03.power*scalar 338957770+ JHk_Rhs04.power*scalar 1758643221+ JHk_Rhs05.power*scalar 1383659086+ JHk_Rhs06.power*scalar 61933653+ JHk_Rhs07.power*scalar 618155599+ JHk_Rhs08.power*scalar 1890494031=⟨⟨1576637415,1666296633⟩,⟨217463890,1777644172⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source59

theorem basis60_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 60=(1297052755 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis60_00

theorem basis60_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 60=(345345951 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis60_01

theorem basis60_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 60=(1508311546 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis60_02

theorem basis60_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 60=(364043303 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis60_03

theorem basis60_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 60=(1045321731 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis60_04

theorem basis60_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 60=(18173074 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis60_05

theorem basis60_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 60=(1837483248 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis60_06

theorem basis60_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 60=(979302764 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis60_07

theorem basis60_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 60=(1353870055 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis60_08

theorem basis60_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 60=(1526249934 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis60_09

theorem source60 : totalAt 10 60=CheckpointBytes5Output.ofK JFq_Weight60.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis60_00,basis60_01,basis60_02,basis60_03,basis60_04,basis60_05,basis60_06,basis60_07,basis60_08,basis60_09]
  change (0 : K)+ (1 : K)*scalar 1297052755+ JHk_Rhs00.power*scalar 345345951+ JHk_Rhs01.power*scalar 1508311546+ JHk_Rhs02.power*scalar 364043303+ JHk_Rhs03.power*scalar 1045321731+ JHk_Rhs04.power*scalar 18173074+ JHk_Rhs05.power*scalar 1837483248+ JHk_Rhs06.power*scalar 979302764+ JHk_Rhs07.power*scalar 1353870055+ JHk_Rhs08.power*scalar 1526249934=⟨⟨301289576,379221294⟩,⟨1825123628,1353143496⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source60

theorem basis61_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 61=(1833778374 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis61_00

theorem basis61_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 61=(1138088989 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis61_01

theorem basis61_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 61=(1990818024 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis61_02

theorem basis61_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 61=(367502514 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis61_03

theorem basis61_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 61=(1587350312 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis61_04

theorem basis61_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 61=(889670066 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis61_05

theorem basis61_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 61=(1802145060 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis61_06

theorem basis61_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 61=(353216071 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis61_07

theorem basis61_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 61=(264693046 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis61_08

theorem basis61_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 61=(453794516 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis61_09

theorem source61 : totalAt 10 61=CheckpointBytes5Output.ofK JFq_Weight61.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis61_00,basis61_01,basis61_02,basis61_03,basis61_04,basis61_05,basis61_06,basis61_07,basis61_08,basis61_09]
  change (0 : K)+ (1 : K)*scalar 1833778374+ JHk_Rhs00.power*scalar 1138088989+ JHk_Rhs01.power*scalar 1990818024+ JHk_Rhs02.power*scalar 367502514+ JHk_Rhs03.power*scalar 1587350312+ JHk_Rhs04.power*scalar 889670066+ JHk_Rhs05.power*scalar 1802145060+ JHk_Rhs06.power*scalar 353216071+ JHk_Rhs07.power*scalar 264693046+ JHk_Rhs08.power*scalar 453794516=⟨⟨1818087377,234435719⟩,⟨1474578401,271929601⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source61

theorem basis62_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 62=(58132495 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis62_00

theorem basis62_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 62=(261447740 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis62_01

theorem basis62_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 62=(2092774411 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis62_02

theorem basis62_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 62=(1904781162 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis62_03

theorem basis62_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 62=(1118618574 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis62_04

theorem basis62_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 62=(1105321276 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis62_05

theorem basis62_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 62=(1197725447 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis62_06

theorem basis62_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 62=(253985105 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis62_07

theorem basis62_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 62=(562056521 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis62_08

theorem basis62_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 62=(1506384994 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis62_09

theorem source62 : totalAt 10 62=CheckpointBytes5Output.ofK JFq_Weight62.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis62_00,basis62_01,basis62_02,basis62_03,basis62_04,basis62_05,basis62_06,basis62_07,basis62_08,basis62_09]
  change (0 : K)+ (1 : K)*scalar 58132495+ JHk_Rhs00.power*scalar 261447740+ JHk_Rhs01.power*scalar 2092774411+ JHk_Rhs02.power*scalar 1904781162+ JHk_Rhs03.power*scalar 1118618574+ JHk_Rhs04.power*scalar 1105321276+ JHk_Rhs05.power*scalar 1197725447+ JHk_Rhs06.power*scalar 253985105+ JHk_Rhs07.power*scalar 562056521+ JHk_Rhs08.power*scalar 1506384994=⟨⟨1523912250,312866993⟩,⟨1949862119,1589077379⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source62
end AspisR1.JHl_Weight59_62
end
