import NDO_JHl_WeightFormula
import RPt_JFq_Weights06
import RPt_JFq_Weights07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight27_30
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis27_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 27=(1257741683 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis27_00

theorem basis27_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 27=(1002261159 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis27_01

theorem basis27_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 27=(1009421093 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis27_02

theorem basis27_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 27=(1230072561 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis27_03

theorem basis27_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 27=(1012976789 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis27_04

theorem basis27_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 27=(1298376968 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis27_05

theorem basis27_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 27=(1617776813 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis27_06

theorem basis27_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 27=(1545735268 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis27_07

theorem basis27_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 27=(1759217536 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis27_08

theorem basis27_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 27=(1415158646 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis27_09

theorem source27 : totalAt 10 27=CheckpointBytes5Output.ofK JFq_Weight27.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis27_00,basis27_01,basis27_02,basis27_03,basis27_04,basis27_05,basis27_06,basis27_07,basis27_08,basis27_09]
  change (0 : K)+ (1 : K)*scalar 1257741683+ JHk_Rhs00.power*scalar 1002261159+ JHk_Rhs01.power*scalar 1009421093+ JHk_Rhs02.power*scalar 1230072561+ JHk_Rhs03.power*scalar 1012976789+ JHk_Rhs04.power*scalar 1298376968+ JHk_Rhs05.power*scalar 1617776813+ JHk_Rhs06.power*scalar 1545735268+ JHk_Rhs07.power*scalar 1759217536+ JHk_Rhs08.power*scalar 1415158646=⟨⟨1176095107,327556127⟩,⟨2123999433,387369717⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source27

theorem basis28_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 28=(1628782243 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis28_00

theorem basis28_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 28=(153574115 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis28_01

theorem basis28_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 28=(1339021947 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis28_02

theorem basis28_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 28=(1740539763 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis28_03

theorem basis28_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 28=(1511583010 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis28_04

theorem basis28_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 28=(2134123671 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis28_05

theorem basis28_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 28=(226093388 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis28_06

theorem basis28_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 28=(1425098913 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis28_07

theorem basis28_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 28=(297369381 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis28_08

theorem basis28_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 28=(1251254129 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis28_09

theorem source28 : totalAt 10 28=CheckpointBytes5Output.ofK JFq_Weight28.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis28_00,basis28_01,basis28_02,basis28_03,basis28_04,basis28_05,basis28_06,basis28_07,basis28_08,basis28_09]
  change (0 : K)+ (1 : K)*scalar 1628782243+ JHk_Rhs00.power*scalar 153574115+ JHk_Rhs01.power*scalar 1339021947+ JHk_Rhs02.power*scalar 1740539763+ JHk_Rhs03.power*scalar 1511583010+ JHk_Rhs04.power*scalar 2134123671+ JHk_Rhs05.power*scalar 226093388+ JHk_Rhs06.power*scalar 1425098913+ JHk_Rhs07.power*scalar 297369381+ JHk_Rhs08.power*scalar 1251254129=⟨⟨1284685638,1713701488⟩,⟨1196712103,673166315⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source28

theorem basis29_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 29=(1944651434 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis29_00

theorem basis29_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 29=(1569106315 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis29_01

theorem basis29_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 29=(1034619386 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis29_02

theorem basis29_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 29=(1991258442 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis29_03

theorem basis29_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 29=(1135665817 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis29_04

theorem basis29_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 29=(537934790 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis29_05

theorem basis29_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 29=(928411239 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis29_06

theorem basis29_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 29=(165307169 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis29_07

theorem basis29_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 29=(401973061 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis29_08

theorem basis29_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 29=(916261067 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis29_09

theorem source29 : totalAt 10 29=CheckpointBytes5Output.ofK JFq_Weight29.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis29_00,basis29_01,basis29_02,basis29_03,basis29_04,basis29_05,basis29_06,basis29_07,basis29_08,basis29_09]
  change (0 : K)+ (1 : K)*scalar 1944651434+ JHk_Rhs00.power*scalar 1569106315+ JHk_Rhs01.power*scalar 1034619386+ JHk_Rhs02.power*scalar 1991258442+ JHk_Rhs03.power*scalar 1135665817+ JHk_Rhs04.power*scalar 537934790+ JHk_Rhs05.power*scalar 928411239+ JHk_Rhs06.power*scalar 165307169+ JHk_Rhs07.power*scalar 401973061+ JHk_Rhs08.power*scalar 916261067=⟨⟨1011626850,1364074309⟩,⟨1911771696,242692980⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source29

theorem basis30_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 30=(403097124 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis30_00

theorem basis30_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 30=(1691243250 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis30_01

theorem basis30_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 30=(1406966088 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis30_02

theorem basis30_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 30=(1464937786 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis30_03

theorem basis30_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 30=(1598431027 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis30_04

theorem basis30_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 30=(2074567954 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis30_05

theorem basis30_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 30=(185327509 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis30_06

theorem basis30_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 30=(1057301984 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis30_07

theorem basis30_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 30=(1153253156 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis30_08

theorem basis30_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 30=(871019863 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis30_09

theorem source30 : totalAt 10 30=CheckpointBytes5Output.ofK JFq_Weight30.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis30_00,basis30_01,basis30_02,basis30_03,basis30_04,basis30_05,basis30_06,basis30_07,basis30_08,basis30_09]
  change (0 : K)+ (1 : K)*scalar 403097124+ JHk_Rhs00.power*scalar 1691243250+ JHk_Rhs01.power*scalar 1406966088+ JHk_Rhs02.power*scalar 1464937786+ JHk_Rhs03.power*scalar 1598431027+ JHk_Rhs04.power*scalar 2074567954+ JHk_Rhs05.power*scalar 185327509+ JHk_Rhs06.power*scalar 1057301984+ JHk_Rhs07.power*scalar 1153253156+ JHk_Rhs08.power*scalar 871019863=⟨⟨1397827463,2065720588⟩,⟨211843219,402797570⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source30
end AspisR1.JHl_Weight27_30
end
