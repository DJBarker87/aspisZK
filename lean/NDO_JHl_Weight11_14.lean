import NDO_JHl_WeightFormula
import RPt_JFq_Weights02
import RPt_JFq_Weights03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight11_14
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis11_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 11=(692495883 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis11_00

theorem basis11_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 11=(1470061749 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis11_01

theorem basis11_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 11=(970314294 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis11_02

theorem basis11_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 11=(543285621 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis11_03

theorem basis11_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 11=(1393358633 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis11_04

theorem basis11_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 11=(1933099905 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis11_05

theorem basis11_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 11=(2043730029 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis11_06

theorem basis11_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 11=(1984497276 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis11_07

theorem basis11_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 11=(1445544209 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis11_08

theorem basis11_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 11=(1388130554 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis11_09

theorem source11 : totalAt 10 11=CheckpointBytes5Output.ofK JFq_Weight11.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis11_00,basis11_01,basis11_02,basis11_03,basis11_04,basis11_05,basis11_06,basis11_07,basis11_08,basis11_09]
  change (0 : K)+ (1 : K)*scalar 692495883+ JHk_Rhs00.power*scalar 1470061749+ JHk_Rhs01.power*scalar 970314294+ JHk_Rhs02.power*scalar 543285621+ JHk_Rhs03.power*scalar 1393358633+ JHk_Rhs04.power*scalar 1933099905+ JHk_Rhs05.power*scalar 2043730029+ JHk_Rhs06.power*scalar 1984497276+ JHk_Rhs07.power*scalar 1445544209+ JHk_Rhs08.power*scalar 1388130554=⟨⟨1733269172,517960228⟩,⟨187618203,1733556446⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source11

theorem basis12_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 12=(808082165 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis12_00

theorem basis12_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 12=(1567975852 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis12_01

theorem basis12_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 12=(1620129760 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis12_02

theorem basis12_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 12=(921772976 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis12_03

theorem basis12_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 12=(1169277051 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis12_04

theorem basis12_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 12=(277457244 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis12_05

theorem basis12_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 12=(861067974 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis12_06

theorem basis12_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 12=(1906927662 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis12_07

theorem basis12_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 12=(130642676 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis12_08

theorem basis12_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 12=(990794350 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis12_09

theorem source12 : totalAt 10 12=CheckpointBytes5Output.ofK JFq_Weight12.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis12_00,basis12_01,basis12_02,basis12_03,basis12_04,basis12_05,basis12_06,basis12_07,basis12_08,basis12_09]
  change (0 : K)+ (1 : K)*scalar 808082165+ JHk_Rhs00.power*scalar 1567975852+ JHk_Rhs01.power*scalar 1620129760+ JHk_Rhs02.power*scalar 921772976+ JHk_Rhs03.power*scalar 1169277051+ JHk_Rhs04.power*scalar 277457244+ JHk_Rhs05.power*scalar 861067974+ JHk_Rhs06.power*scalar 1906927662+ JHk_Rhs07.power*scalar 130642676+ JHk_Rhs08.power*scalar 990794350=⟨⟨604332078,1601308930⟩,⟨919930871,742751204⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source12

theorem basis13_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 13=(399241202 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis13_00

theorem basis13_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 13=(1295792201 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis13_01

theorem basis13_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 13=(240649911 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis13_02

theorem basis13_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 13=(573907507 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis13_03

theorem basis13_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 13=(1138257544 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis13_04

theorem basis13_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 13=(1950362741 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis13_05

theorem basis13_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 13=(904990689 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis13_06

theorem basis13_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 13=(1792732176 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis13_07

theorem basis13_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 13=(1658229896 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis13_08

theorem basis13_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 13=(429354850 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis13_09

theorem source13 : totalAt 10 13=CheckpointBytes5Output.ofK JFq_Weight13.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis13_00,basis13_01,basis13_02,basis13_03,basis13_04,basis13_05,basis13_06,basis13_07,basis13_08,basis13_09]
  change (0 : K)+ (1 : K)*scalar 399241202+ JHk_Rhs00.power*scalar 1295792201+ JHk_Rhs01.power*scalar 240649911+ JHk_Rhs02.power*scalar 573907507+ JHk_Rhs03.power*scalar 1138257544+ JHk_Rhs04.power*scalar 1950362741+ JHk_Rhs05.power*scalar 904990689+ JHk_Rhs06.power*scalar 1792732176+ JHk_Rhs07.power*scalar 1658229896+ JHk_Rhs08.power*scalar 429354850=⟨⟨38688320,583580151⟩,⟨724538461,46343736⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source13

theorem basis14_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 14=(509699118 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis14_00

theorem basis14_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 14=(546226348 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis14_01

theorem basis14_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 14=(74141257 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis14_02

theorem basis14_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 14=(446154862 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis14_03

theorem basis14_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 14=(1273668760 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis14_04

theorem basis14_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 14=(74444448 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis14_05

theorem basis14_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 14=(681931576 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis14_06

theorem basis14_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 14=(652001410 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis14_07

theorem basis14_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 14=(417808027 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis14_08

theorem basis14_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 14=(1150700794 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis14_09

theorem source14 : totalAt 10 14=CheckpointBytes5Output.ofK JFq_Weight14.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis14_00,basis14_01,basis14_02,basis14_03,basis14_04,basis14_05,basis14_06,basis14_07,basis14_08,basis14_09]
  change (0 : K)+ (1 : K)*scalar 509699118+ JHk_Rhs00.power*scalar 546226348+ JHk_Rhs01.power*scalar 74141257+ JHk_Rhs02.power*scalar 446154862+ JHk_Rhs03.power*scalar 1273668760+ JHk_Rhs04.power*scalar 74444448+ JHk_Rhs05.power*scalar 681931576+ JHk_Rhs06.power*scalar 652001410+ JHk_Rhs07.power*scalar 417808027+ JHk_Rhs08.power*scalar 1150700794=⟨⟨770298800,148307436⟩,⟨1195650966,97477188⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source14
end AspisR1.JHl_Weight11_14
end
