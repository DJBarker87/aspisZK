import NDO_JHl_WeightFormula
import RPt_JFq_Weights00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight01_02
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis01_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 1=(2111287037 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis01_00

theorem basis01_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 1=(675540732 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis01_01

theorem basis01_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 1=(1734224569 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis01_02

theorem basis01_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 1=(548654413 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis01_03

theorem basis01_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 1=(703356619 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis01_04

theorem basis01_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 1=(2117129771 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis01_05

theorem basis01_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 1=(1520716407 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis01_06

theorem basis01_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 1=(974019107 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis01_07

theorem basis01_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 1=(308503456 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis01_08

theorem basis01_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 1=(1601993573 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis01_09

theorem source01 : totalAt 10 1=CheckpointBytes5Output.ofK JFq_Weight01.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis01_00,basis01_01,basis01_02,basis01_03,basis01_04,basis01_05,basis01_06,basis01_07,basis01_08,basis01_09]
  change (0 : K)+ (1 : K)*scalar 2111287037+ JHk_Rhs00.power*scalar 675540732+ JHk_Rhs01.power*scalar 1734224569+ JHk_Rhs02.power*scalar 548654413+ JHk_Rhs03.power*scalar 703356619+ JHk_Rhs04.power*scalar 2117129771+ JHk_Rhs05.power*scalar 1520716407+ JHk_Rhs06.power*scalar 974019107+ JHk_Rhs07.power*scalar 308503456+ JHk_Rhs08.power*scalar 1601993573=⟨⟨472744332,780419209⟩,⟨692595632,960207255⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source01

theorem basis02_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 2=(1687627388 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis02_00

theorem basis02_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 2=(123224822 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis02_01

theorem basis02_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 2=(820909939 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis02_02

theorem basis02_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 2=(224041153 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis02_03

theorem basis02_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 2=(2050600032 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis02_04

theorem basis02_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 2=(661145344 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis02_05

theorem basis02_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 2=(1419886030 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis02_06

theorem basis02_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 2=(1674266664 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis02_07

theorem basis02_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 2=(1850919521 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis02_08

theorem basis02_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 2=(85650469 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis02_09

theorem source02 : totalAt 10 2=CheckpointBytes5Output.ofK JFq_Weight02.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis02_00,basis02_01,basis02_02,basis02_03,basis02_04,basis02_05,basis02_06,basis02_07,basis02_08,basis02_09]
  change (0 : K)+ (1 : K)*scalar 1687627388+ JHk_Rhs00.power*scalar 123224822+ JHk_Rhs01.power*scalar 820909939+ JHk_Rhs02.power*scalar 224041153+ JHk_Rhs03.power*scalar 2050600032+ JHk_Rhs04.power*scalar 661145344+ JHk_Rhs05.power*scalar 1419886030+ JHk_Rhs06.power*scalar 1674266664+ JHk_Rhs07.power*scalar 1850919521+ JHk_Rhs08.power*scalar 85650469=⟨⟨98251795,1930821505⟩,⟨747250178,61916910⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source02
end AspisR1.JHl_Weight01_02
end
