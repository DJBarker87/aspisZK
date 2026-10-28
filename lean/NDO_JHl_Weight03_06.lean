import NDO_JHl_WeightFormula
import RPt_JFq_Weights00
import RPt_JFq_Weights01
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight03_06
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis03_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 3=(1720871816 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis03_00

theorem basis03_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 3=(1104419070 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis03_01

theorem basis03_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 3=(1956996647 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis03_02

theorem basis03_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 3=(49211226 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis03_03

theorem basis03_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 3=(160374321 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis03_04

theorem basis03_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 3=(1085774830 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis03_05

theorem basis03_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 3=(1475551406 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis03_06

theorem basis03_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 3=(1268529836 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis03_07

theorem basis03_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 3=(492719612 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis03_08

theorem basis03_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 3=(332391389 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis03_09

theorem source03 : totalAt 10 3=CheckpointBytes5Output.ofK JFq_Weight03.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis03_00,basis03_01,basis03_02,basis03_03,basis03_04,basis03_05,basis03_06,basis03_07,basis03_08,basis03_09]
  change (0 : K)+ (1 : K)*scalar 1720871816+ JHk_Rhs00.power*scalar 1104419070+ JHk_Rhs01.power*scalar 1956996647+ JHk_Rhs02.power*scalar 49211226+ JHk_Rhs03.power*scalar 160374321+ JHk_Rhs04.power*scalar 1085774830+ JHk_Rhs05.power*scalar 1475551406+ JHk_Rhs06.power*scalar 1268529836+ JHk_Rhs07.power*scalar 492719612+ JHk_Rhs08.power*scalar 332391389=⟨⟨864310848,1199973361⟩,⟨1739684998,1270745853⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source03

theorem basis04_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 4=(909890909 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis04_00

theorem basis04_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 4=(505368869 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis04_01

theorem basis04_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 4=(492590140 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis04_02

theorem basis04_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 4=(1014813006 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis04_03

theorem basis04_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 4=(1460559143 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis04_04

theorem basis04_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 4=(530956398 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis04_05

theorem basis04_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 4=(1670762117 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis04_06

theorem basis04_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 4=(52984170 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis04_07

theorem basis04_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 4=(40858697 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis04_08

theorem basis04_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 4=(119061226 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis04_09

theorem source04 : totalAt 10 4=CheckpointBytes5Output.ofK JFq_Weight04.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis04_00,basis04_01,basis04_02,basis04_03,basis04_04,basis04_05,basis04_06,basis04_07,basis04_08,basis04_09]
  change (0 : K)+ (1 : K)*scalar 909890909+ JHk_Rhs00.power*scalar 505368869+ JHk_Rhs01.power*scalar 492590140+ JHk_Rhs02.power*scalar 1014813006+ JHk_Rhs03.power*scalar 1460559143+ JHk_Rhs04.power*scalar 530956398+ JHk_Rhs05.power*scalar 1670762117+ JHk_Rhs06.power*scalar 52984170+ JHk_Rhs07.power*scalar 40858697+ JHk_Rhs08.power*scalar 119061226=⟨⟨459072339,1075132793⟩,⟨451460549,605968709⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source04

theorem basis05_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 5=(328459243 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis05_00

theorem basis05_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 5=(1382878313 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis05_01

theorem basis05_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 5=(122199231 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis05_02

theorem basis05_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 5=(1311020634 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis05_03

theorem basis05_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 5=(168791224 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis05_04

theorem basis05_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 5=(931562242 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis05_05

theorem basis05_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 5=(1846450408 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis05_06

theorem basis05_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 5=(1383239464 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis05_07

theorem basis05_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 5=(976582931 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis05_08

theorem basis05_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 5=(322137560 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis05_09

theorem source05 : totalAt 10 5=CheckpointBytes5Output.ofK JFq_Weight05.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis05_00,basis05_01,basis05_02,basis05_03,basis05_04,basis05_05,basis05_06,basis05_07,basis05_08,basis05_09]
  change (0 : K)+ (1 : K)*scalar 328459243+ JHk_Rhs00.power*scalar 1382878313+ JHk_Rhs01.power*scalar 122199231+ JHk_Rhs02.power*scalar 1311020634+ JHk_Rhs03.power*scalar 168791224+ JHk_Rhs04.power*scalar 931562242+ JHk_Rhs05.power*scalar 1846450408+ JHk_Rhs06.power*scalar 1383239464+ JHk_Rhs07.power*scalar 976582931+ JHk_Rhs08.power*scalar 322137560=⟨⟨1187431572,1254244807⟩,⟨819530238,1155525899⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source05

theorem basis06_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 6=(2132865184 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis06_00

theorem basis06_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 6=(1853226823 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis06_01

theorem basis06_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 6=(386693016 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis06_02

theorem basis06_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 6=(1209768194 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis06_03

theorem basis06_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 6=(1925778699 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis06_04

theorem basis06_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 6=(1892469467 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis06_05

theorem basis06_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 6=(58820007 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis06_06

theorem basis06_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 6=(670898800 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis06_07

theorem basis06_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 6=(2105017559 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis06_08

theorem basis06_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 6=(1626288444 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis06_09

theorem source06 : totalAt 10 6=CheckpointBytes5Output.ofK JFq_Weight06.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis06_00,basis06_01,basis06_02,basis06_03,basis06_04,basis06_05,basis06_06,basis06_07,basis06_08,basis06_09]
  change (0 : K)+ (1 : K)*scalar 2132865184+ JHk_Rhs00.power*scalar 1853226823+ JHk_Rhs01.power*scalar 386693016+ JHk_Rhs02.power*scalar 1209768194+ JHk_Rhs03.power*scalar 1925778699+ JHk_Rhs04.power*scalar 1892469467+ JHk_Rhs05.power*scalar 58820007+ JHk_Rhs06.power*scalar 670898800+ JHk_Rhs07.power*scalar 2105017559+ JHk_Rhs08.power*scalar 1626288444=⟨⟨782346679,1528519116⟩,⟨1792517043,1947315940⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source06
end AspisR1.JHl_Weight03_06
end
