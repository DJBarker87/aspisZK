import NDO_JHl_WeightFormula
import RPt_JFq_Weights10
import RPt_JFq_Weights11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight43_46
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis43_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 43=(2110212105 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis43_00

theorem basis43_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 43=(273738045 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis43_01

theorem basis43_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 43=(1104723807 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis43_02

theorem basis43_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 43=(443196859 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis43_03

theorem basis43_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 43=(666108368 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis43_04

theorem basis43_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 43=(2085056343 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis43_05

theorem basis43_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 43=(24446380 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis43_06

theorem basis43_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 43=(1817473666 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis43_07

theorem basis43_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 43=(1483754924 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis43_08

theorem basis43_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 43=(611010831 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis43_09

theorem source43 : totalAt 10 43=CheckpointBytes5Output.ofK JFq_Weight43.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis43_00,basis43_01,basis43_02,basis43_03,basis43_04,basis43_05,basis43_06,basis43_07,basis43_08,basis43_09]
  change (0 : K)+ (1 : K)*scalar 2110212105+ JHk_Rhs00.power*scalar 273738045+ JHk_Rhs01.power*scalar 1104723807+ JHk_Rhs02.power*scalar 443196859+ JHk_Rhs03.power*scalar 666108368+ JHk_Rhs04.power*scalar 2085056343+ JHk_Rhs05.power*scalar 24446380+ JHk_Rhs06.power*scalar 1817473666+ JHk_Rhs07.power*scalar 1483754924+ JHk_Rhs08.power*scalar 611010831=⟨⟨1169207875,1140491595⟩,⟨959133084,1330119488⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source43

theorem basis44_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 44=(720623393 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis44_00

theorem basis44_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 44=(950691270 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis44_01

theorem basis44_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 44=(1594946508 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis44_02

theorem basis44_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 44=(42988948 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis44_03

theorem basis44_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 44=(112387453 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis44_04

theorem basis44_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 44=(1616157126 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis44_05

theorem basis44_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 44=(1156219360 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis44_06

theorem basis44_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 44=(1332128770 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis44_07

theorem basis44_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 44=(1060827624 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis44_08

theorem basis44_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 44=(177692517 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis44_09

theorem source44 : totalAt 10 44=CheckpointBytes5Output.ofK JFq_Weight44.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis44_00,basis44_01,basis44_02,basis44_03,basis44_04,basis44_05,basis44_06,basis44_07,basis44_08,basis44_09]
  change (0 : K)+ (1 : K)*scalar 720623393+ JHk_Rhs00.power*scalar 950691270+ JHk_Rhs01.power*scalar 1594946508+ JHk_Rhs02.power*scalar 42988948+ JHk_Rhs03.power*scalar 112387453+ JHk_Rhs04.power*scalar 1616157126+ JHk_Rhs05.power*scalar 1156219360+ JHk_Rhs06.power*scalar 1332128770+ JHk_Rhs07.power*scalar 1060827624+ JHk_Rhs08.power*scalar 177692517=⟨⟨2104496606,2040082342⟩,⟨605290773,1149965857⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source44

theorem basis45_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 45=(589662719 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis45_00

theorem basis45_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 45=(1459590579 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis45_01

theorem basis45_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 45=(1626159816 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis45_02

theorem basis45_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 45=(1142421590 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis45_03

theorem basis45_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 45=(378375278 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis45_04

theorem basis45_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 45=(249127049 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis45_05

theorem basis45_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 45=(1994028799 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis45_06

theorem basis45_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 45=(1939973467 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis45_07

theorem basis45_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 45=(909200338 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis45_08

theorem basis45_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 45=(543215488 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis45_09

theorem source45 : totalAt 10 45=CheckpointBytes5Output.ofK JFq_Weight45.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis45_00,basis45_01,basis45_02,basis45_03,basis45_04,basis45_05,basis45_06,basis45_07,basis45_08,basis45_09]
  change (0 : K)+ (1 : K)*scalar 589662719+ JHk_Rhs00.power*scalar 1459590579+ JHk_Rhs01.power*scalar 1626159816+ JHk_Rhs02.power*scalar 1142421590+ JHk_Rhs03.power*scalar 378375278+ JHk_Rhs04.power*scalar 249127049+ JHk_Rhs05.power*scalar 1994028799+ JHk_Rhs06.power*scalar 1939973467+ JHk_Rhs07.power*scalar 909200338+ JHk_Rhs08.power*scalar 543215488=⟨⟨1508504349,1621359132⟩,⟨1923088544,1734003233⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source45

theorem basis46_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 46=(1782796959 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis46_00

theorem basis46_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 46=(1263221919 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis46_01

theorem basis46_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 46=(1183058176 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis46_02

theorem basis46_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 46=(1118073804 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis46_03

theorem basis46_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 46=(1719702090 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis46_04

theorem basis46_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 46=(918432518 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis46_05

theorem basis46_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 46=(1913117859 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis46_06

theorem basis46_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 46=(837350129 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis46_07

theorem basis46_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 46=(1527137927 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis46_08

theorem basis46_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 46=(1031801244 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis46_09

theorem source46 : totalAt 10 46=CheckpointBytes5Output.ofK JFq_Weight46.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis46_00,basis46_01,basis46_02,basis46_03,basis46_04,basis46_05,basis46_06,basis46_07,basis46_08,basis46_09]
  change (0 : K)+ (1 : K)*scalar 1782796959+ JHk_Rhs00.power*scalar 1263221919+ JHk_Rhs01.power*scalar 1183058176+ JHk_Rhs02.power*scalar 1118073804+ JHk_Rhs03.power*scalar 1719702090+ JHk_Rhs04.power*scalar 918432518+ JHk_Rhs05.power*scalar 1913117859+ JHk_Rhs06.power*scalar 837350129+ JHk_Rhs07.power*scalar 1527137927+ JHk_Rhs08.power*scalar 1031801244=⟨⟨1327398296,1203506035⟩,⟨1627765203,1402988272⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source46
end AspisR1.JHl_Weight43_46
end
