import NDO_JHl_WeightFormula
import RPt_JFq_Weights13
import RPt_JFq_Weights14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight55_58
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis55_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 55=(552112968 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis55_00

theorem basis55_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 55=(1846147795 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis55_01

theorem basis55_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 55=(1987739306 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis55_02

theorem basis55_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 55=(955261058 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis55_03

theorem basis55_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 55=(1156142692 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis55_04

theorem basis55_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 55=(69544934 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis55_05

theorem basis55_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 55=(2042902496 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis55_06

theorem basis55_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 55=(787500668 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis55_07

theorem basis55_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 55=(1875082709 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis55_08

theorem basis55_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 55=(880436275 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis55_09

theorem source55 : totalAt 10 55=CheckpointBytes5Output.ofK JFq_Weight55.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis55_00,basis55_01,basis55_02,basis55_03,basis55_04,basis55_05,basis55_06,basis55_07,basis55_08,basis55_09]
  change (0 : K)+ (1 : K)*scalar 552112968+ JHk_Rhs00.power*scalar 1846147795+ JHk_Rhs01.power*scalar 1987739306+ JHk_Rhs02.power*scalar 955261058+ JHk_Rhs03.power*scalar 1156142692+ JHk_Rhs04.power*scalar 69544934+ JHk_Rhs05.power*scalar 2042902496+ JHk_Rhs06.power*scalar 787500668+ JHk_Rhs07.power*scalar 1875082709+ JHk_Rhs08.power*scalar 880436275=⟨⟨197076199,40523232⟩,⟨503071546,1735787385⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source55

theorem basis56_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 56=(2147359070 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis56_00

theorem basis56_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 56=(1185222313 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis56_01

theorem basis56_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 56=(19470048 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis56_02

theorem basis56_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 56=(164984346 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis56_03

theorem basis56_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 56=(1253776630 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis56_04

theorem basis56_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 56=(1312109001 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis56_05

theorem basis56_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 56=(707984477 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis56_06

theorem basis56_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 56=(1811948042 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis56_07

theorem basis56_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 56=(1317987202 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis56_08

theorem basis56_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 56=(224749340 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis56_09

theorem source56 : totalAt 10 56=CheckpointBytes5Output.ofK JFq_Weight56.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis56_00,basis56_01,basis56_02,basis56_03,basis56_04,basis56_05,basis56_06,basis56_07,basis56_08,basis56_09]
  change (0 : K)+ (1 : K)*scalar 2147359070+ JHk_Rhs00.power*scalar 1185222313+ JHk_Rhs01.power*scalar 19470048+ JHk_Rhs02.power*scalar 164984346+ JHk_Rhs03.power*scalar 1253776630+ JHk_Rhs04.power*scalar 1312109001+ JHk_Rhs05.power*scalar 707984477+ JHk_Rhs06.power*scalar 1811948042+ JHk_Rhs07.power*scalar 1317987202+ JHk_Rhs08.power*scalar 224749340=⟨⟨583486090,276206717⟩,⟨581871196,1524717007⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source56

theorem basis57_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 57=(1696908917 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis57_00

theorem basis57_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 57=(1385144124 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis57_01

theorem basis57_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 57=(463614680 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis57_02

theorem basis57_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 57=(997754273 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis57_03

theorem basis57_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 57=(675560110 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis57_04

theorem basis57_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 57=(727160467 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis57_05

theorem basis57_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 57=(1444689036 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis57_06

theorem basis57_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 57=(562321116 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis57_07

theorem basis57_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 57=(98078439 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis57_08

theorem basis57_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 57=(1629121464 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis57_09

theorem source57 : totalAt 10 57=CheckpointBytes5Output.ofK JFq_Weight57.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis57_00,basis57_01,basis57_02,basis57_03,basis57_04,basis57_05,basis57_06,basis57_07,basis57_08,basis57_09]
  change (0 : K)+ (1 : K)*scalar 1696908917+ JHk_Rhs00.power*scalar 1385144124+ JHk_Rhs01.power*scalar 463614680+ JHk_Rhs02.power*scalar 997754273+ JHk_Rhs03.power*scalar 675560110+ JHk_Rhs04.power*scalar 727160467+ JHk_Rhs05.power*scalar 1444689036+ JHk_Rhs06.power*scalar 562321116+ JHk_Rhs07.power*scalar 98078439+ JHk_Rhs08.power*scalar 1629121464=⟨⟨1780737754,1253710700⟩,⟨1205871765,830468577⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source57

theorem basis58_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 58=(1239410071 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis58_00

theorem basis58_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 58=(495543714 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis58_01

theorem basis58_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 58=(2067068880 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis58_02

theorem basis58_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 58=(3677548 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis58_03

theorem basis58_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 58=(868362193 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis58_04

theorem basis58_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 58=(831171269 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis58_05

theorem basis58_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 58=(1874560039 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis58_06

theorem basis58_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 58=(431603964 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis58_07

theorem basis58_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 58=(50488197 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis58_08

theorem basis58_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 58=(1880522338 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis58_09

theorem source58 : totalAt 10 58=CheckpointBytes5Output.ofK JFq_Weight58.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis58_00,basis58_01,basis58_02,basis58_03,basis58_04,basis58_05,basis58_06,basis58_07,basis58_08,basis58_09]
  change (0 : K)+ (1 : K)*scalar 1239410071+ JHk_Rhs00.power*scalar 495543714+ JHk_Rhs01.power*scalar 2067068880+ JHk_Rhs02.power*scalar 3677548+ JHk_Rhs03.power*scalar 868362193+ JHk_Rhs04.power*scalar 831171269+ JHk_Rhs05.power*scalar 1874560039+ JHk_Rhs06.power*scalar 431603964+ JHk_Rhs07.power*scalar 50488197+ JHk_Rhs08.power*scalar 1880522338=⟨⟨837099947,1579278096⟩,⟨983244076,81628231⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source58
end AspisR1.JHl_Weight55_58
end
