import NDO_JHl_WeightFormula
import RPt_JFq_Weights03
import RPt_JFq_Weights04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight15_18
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis15_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 15=(1859621481 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis15_00

theorem basis15_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 15=(451376392 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis15_01

theorem basis15_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 15=(1841505798 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis15_02

theorem basis15_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 15=(1994173466 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis15_03

theorem basis15_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 15=(142454297 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis15_04

theorem basis15_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 15=(1386657067 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis15_05

theorem basis15_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 15=(1423916972 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis15_06

theorem basis15_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 15=(2023254147 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis15_07

theorem basis15_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 15=(490859754 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis15_08

theorem basis15_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 15=(143310205 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis15_09

theorem source15 : totalAt 10 15=CheckpointBytes5Output.ofK JFq_Weight15.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis15_00,basis15_01,basis15_02,basis15_03,basis15_04,basis15_05,basis15_06,basis15_07,basis15_08,basis15_09]
  change (0 : K)+ (1 : K)*scalar 1859621481+ JHk_Rhs00.power*scalar 451376392+ JHk_Rhs01.power*scalar 1841505798+ JHk_Rhs02.power*scalar 1994173466+ JHk_Rhs03.power*scalar 142454297+ JHk_Rhs04.power*scalar 1386657067+ JHk_Rhs05.power*scalar 1423916972+ JHk_Rhs06.power*scalar 2023254147+ JHk_Rhs07.power*scalar 490859754+ JHk_Rhs08.power*scalar 143310205=⟨⟨1995181154,1582953223⟩,⟨926851,1545436219⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source15

theorem basis16_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 16=(1628383649 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis16_00

theorem basis16_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 16=(2043919630 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis16_01

theorem basis16_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 16=(902201605 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis16_02

theorem basis16_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 16=(238086242 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis16_03

theorem basis16_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 16=(319488558 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis16_04

theorem basis16_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 16=(19455748 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis16_05

theorem basis16_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 16=(829529542 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis16_06

theorem basis16_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 16=(1046339443 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis16_07

theorem basis16_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 16=(1094233749 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis16_08

theorem basis16_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 16=(122649463 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis16_09

theorem source16 : totalAt 10 16=CheckpointBytes5Output.ofK JFq_Weight16.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis16_00,basis16_01,basis16_02,basis16_03,basis16_04,basis16_05,basis16_06,basis16_07,basis16_08,basis16_09]
  change (0 : K)+ (1 : K)*scalar 1628383649+ JHk_Rhs00.power*scalar 2043919630+ JHk_Rhs01.power*scalar 902201605+ JHk_Rhs02.power*scalar 238086242+ JHk_Rhs03.power*scalar 319488558+ JHk_Rhs04.power*scalar 19455748+ JHk_Rhs05.power*scalar 829529542+ JHk_Rhs06.power*scalar 1046339443+ JHk_Rhs07.power*scalar 1094233749+ JHk_Rhs08.power*scalar 122649463=⟨⟨1368938237,1655148581⟩,⟨1133374654,2128059858⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source16

theorem basis17_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 17=(753593581 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis17_00

theorem basis17_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 17=(388886823 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis17_01

theorem basis17_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 17=(2078366248 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis17_02

theorem basis17_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 17=(787646650 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis17_03

theorem basis17_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 17=(187453331 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis17_04

theorem basis17_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 17=(640645752 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis17_05

theorem basis17_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 17=(625405007 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis17_06

theorem basis17_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 17=(1777828392 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis17_07

theorem basis17_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 17=(904812871 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis17_08

theorem basis17_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 17=(247856289 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis17_09

theorem source17 : totalAt 10 17=CheckpointBytes5Output.ofK JFq_Weight17.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis17_00,basis17_01,basis17_02,basis17_03,basis17_04,basis17_05,basis17_06,basis17_07,basis17_08,basis17_09]
  change (0 : K)+ (1 : K)*scalar 753593581+ JHk_Rhs00.power*scalar 388886823+ JHk_Rhs01.power*scalar 2078366248+ JHk_Rhs02.power*scalar 787646650+ JHk_Rhs03.power*scalar 187453331+ JHk_Rhs04.power*scalar 640645752+ JHk_Rhs05.power*scalar 625405007+ JHk_Rhs06.power*scalar 1777828392+ JHk_Rhs07.power*scalar 904812871+ JHk_Rhs08.power*scalar 247856289=⟨⟨1605847887,1561669595⟩,⟨801725198,503020521⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source17

theorem basis18_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 18=(29590932 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis18_00

theorem basis18_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 18=(235068696 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis18_01

theorem basis18_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 18=(1962401682 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis18_02

theorem basis18_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 18=(1791517902 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis18_03

theorem basis18_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 18=(67423200 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis18_04

theorem basis18_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 18=(198541773 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis18_05

theorem basis18_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 18=(2099195159 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis18_06

theorem basis18_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 18=(2136205523 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis18_07

theorem basis18_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 18=(439131628 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis18_08

theorem basis18_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 18=(833564839 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis18_09

theorem source18 : totalAt 10 18=CheckpointBytes5Output.ofK JFq_Weight18.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis18_00,basis18_01,basis18_02,basis18_03,basis18_04,basis18_05,basis18_06,basis18_07,basis18_08,basis18_09]
  change (0 : K)+ (1 : K)*scalar 29590932+ JHk_Rhs00.power*scalar 235068696+ JHk_Rhs01.power*scalar 1962401682+ JHk_Rhs02.power*scalar 1791517902+ JHk_Rhs03.power*scalar 67423200+ JHk_Rhs04.power*scalar 198541773+ JHk_Rhs05.power*scalar 2099195159+ JHk_Rhs06.power*scalar 2136205523+ JHk_Rhs07.power*scalar 439131628+ JHk_Rhs08.power*scalar 833564839=⟨⟨89086899,487081191⟩,⟨71185754,189226593⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source18
end AspisR1.JHl_Weight15_18
end
