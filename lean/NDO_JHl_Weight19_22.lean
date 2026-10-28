import NDO_JHl_WeightFormula
import RPt_JFq_Weights04
import RPt_JFq_Weights05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight19_22
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis19_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 19=(403539082 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis19_00

theorem basis19_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 19=(370034784 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis19_01

theorem basis19_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 19=(1709180796 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis19_02

theorem basis19_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 19=(1850826923 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis19_03

theorem basis19_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 19=(1182457791 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis19_04

theorem basis19_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 19=(1064885010 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis19_05

theorem basis19_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 19=(2111643681 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis19_06

theorem basis19_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 19=(731729712 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis19_07

theorem basis19_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 19=(1258000534 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis19_08

theorem basis19_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 19=(1970456219 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis19_09

theorem source19 : totalAt 10 19=CheckpointBytes5Output.ofK JFq_Weight19.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis19_00,basis19_01,basis19_02,basis19_03,basis19_04,basis19_05,basis19_06,basis19_07,basis19_08,basis19_09]
  change (0 : K)+ (1 : K)*scalar 403539082+ JHk_Rhs00.power*scalar 370034784+ JHk_Rhs01.power*scalar 1709180796+ JHk_Rhs02.power*scalar 1850826923+ JHk_Rhs03.power*scalar 1182457791+ JHk_Rhs04.power*scalar 1064885010+ JHk_Rhs05.power*scalar 2111643681+ JHk_Rhs06.power*scalar 731729712+ JHk_Rhs07.power*scalar 1258000534+ JHk_Rhs08.power*scalar 1970456219=⟨⟨1690206100,36023164⟩,⟨373481768,1416006266⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source19

theorem basis20_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 20=(392157396 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis20_00

theorem basis20_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 20=(1070149592 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis20_01

theorem basis20_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 20=(939369591 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis20_02

theorem basis20_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 20=(1321964383 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis20_03

theorem basis20_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 20=(871344525 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis20_04

theorem basis20_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 20=(1622161960 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis20_05

theorem basis20_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 20=(699533805 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis20_06

theorem basis20_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 20=(1979567192 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis20_07

theorem basis20_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 20=(639498655 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis20_08

theorem basis20_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 20=(1122702106 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis20_09

theorem source20 : totalAt 10 20=CheckpointBytes5Output.ofK JFq_Weight20.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis20_00,basis20_01,basis20_02,basis20_03,basis20_04,basis20_05,basis20_06,basis20_07,basis20_08,basis20_09]
  change (0 : K)+ (1 : K)*scalar 392157396+ JHk_Rhs00.power*scalar 1070149592+ JHk_Rhs01.power*scalar 939369591+ JHk_Rhs02.power*scalar 1321964383+ JHk_Rhs03.power*scalar 871344525+ JHk_Rhs04.power*scalar 1622161960+ JHk_Rhs05.power*scalar 699533805+ JHk_Rhs06.power*scalar 1979567192+ JHk_Rhs07.power*scalar 639498655+ JHk_Rhs08.power*scalar 1122702106=⟨⟨1147110517,1440701546⟩,⟨1879628027,784621982⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source20

theorem basis21_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 21=(1948278325 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis21_00

theorem basis21_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 21=(773759482 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis21_01

theorem basis21_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 21=(87075660 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis21_02

theorem basis21_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 21=(936180348 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis21_03

theorem basis21_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 21=(592176501 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis21_04

theorem basis21_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 21=(84513237 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis21_05

theorem basis21_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 21=(603705988 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis21_06

theorem basis21_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 21=(769530745 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis21_07

theorem basis21_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 21=(641421396 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis21_08

theorem basis21_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 21=(1903137708 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis21_09

theorem source21 : totalAt 10 21=CheckpointBytes5Output.ofK JFq_Weight21.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis21_00,basis21_01,basis21_02,basis21_03,basis21_04,basis21_05,basis21_06,basis21_07,basis21_08,basis21_09]
  change (0 : K)+ (1 : K)*scalar 1948278325+ JHk_Rhs00.power*scalar 773759482+ JHk_Rhs01.power*scalar 87075660+ JHk_Rhs02.power*scalar 936180348+ JHk_Rhs03.power*scalar 592176501+ JHk_Rhs04.power*scalar 84513237+ JHk_Rhs05.power*scalar 603705988+ JHk_Rhs06.power*scalar 769530745+ JHk_Rhs07.power*scalar 641421396+ JHk_Rhs08.power*scalar 1903137708=⟨⟨500874457,105242229⟩,⟨210864545,1900165980⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source21

theorem basis22_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 22=(1409743406 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis22_00

theorem basis22_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 22=(127051229 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis22_01

theorem basis22_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 22=(1019270657 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis22_02

theorem basis22_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 22=(1905849538 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis22_03

theorem basis22_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 22=(600253733 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis22_04

theorem basis22_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 22=(908430985 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis22_05

theorem basis22_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 22=(473332734 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis22_06

theorem basis22_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 22=(1055284434 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis22_07

theorem basis22_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 22=(1799484 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis22_08

theorem basis22_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 22=(1457847477 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis22_09

theorem source22 : totalAt 10 22=CheckpointBytes5Output.ofK JFq_Weight22.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis22_00,basis22_01,basis22_02,basis22_03,basis22_04,basis22_05,basis22_06,basis22_07,basis22_08,basis22_09]
  change (0 : K)+ (1 : K)*scalar 1409743406+ JHk_Rhs00.power*scalar 127051229+ JHk_Rhs01.power*scalar 1019270657+ JHk_Rhs02.power*scalar 1905849538+ JHk_Rhs03.power*scalar 600253733+ JHk_Rhs04.power*scalar 908430985+ JHk_Rhs05.power*scalar 473332734+ JHk_Rhs06.power*scalar 1055284434+ JHk_Rhs07.power*scalar 1799484+ JHk_Rhs08.power*scalar 1457847477=⟨⟨1880987440,351555345⟩,⟨280103724,1330148876⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source22
end AspisR1.JHl_Weight19_22
end
