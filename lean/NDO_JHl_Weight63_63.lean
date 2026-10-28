import NDO_JHl_WeightFormula
import RPt_JFq_Weights15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight63_63
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis63_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 63=(1864252765 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis63_00

theorem basis63_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 63=(1260222059 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis63_01

theorem basis63_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 63=(487222889 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis63_02

theorem basis63_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 63=(4841968 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis63_03

theorem basis63_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 63=(1688428283 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis63_04

theorem basis63_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 63=(605276618 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis63_05

theorem basis63_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 63=(1956302565 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis63_06

theorem basis63_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 63=(10285367 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis63_07

theorem basis63_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 63=(404657869 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis63_08

theorem basis63_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 63=(723565721 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis63_09

theorem source63 : totalAt 10 63=CheckpointBytes5Output.ofK JFq_Weight63.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis63_00,basis63_01,basis63_02,basis63_03,basis63_04,basis63_05,basis63_06,basis63_07,basis63_08,basis63_09]
  change (0 : K)+ (1 : K)*scalar 1864252765+ JHk_Rhs00.power*scalar 1260222059+ JHk_Rhs01.power*scalar 487222889+ JHk_Rhs02.power*scalar 4841968+ JHk_Rhs03.power*scalar 1688428283+ JHk_Rhs04.power*scalar 605276618+ JHk_Rhs05.power*scalar 1956302565+ JHk_Rhs06.power*scalar 10285367+ JHk_Rhs07.power*scalar 404657869+ JHk_Rhs08.power*scalar 723565721=⟨⟨1432735874,893637472⟩,⟨1102055191,260579375⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source63
end AspisR1.JHl_Weight63_63
end
