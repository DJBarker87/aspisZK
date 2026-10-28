import NDO_JHl_WeightFormula
import RPt_JFq_Weights01
import RPt_JFq_Weights02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight07_10
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis07_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 7=(980873277 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis07_00

theorem basis07_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 7=(2043661226 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis07_01

theorem basis07_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 7=(1477335533 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis07_02

theorem basis07_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 7=(413519898 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis07_03

theorem basis07_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 7=(1190379416 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis07_04

theorem basis07_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 7=(1715324417 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis07_05

theorem basis07_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 7=(1766783127 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis07_06

theorem basis07_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 7=(1462315298 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis07_07

theorem basis07_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 7=(1678604425 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis07_08

theorem basis07_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 7=(275123297 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis07_09

theorem source07 : totalAt 10 7=CheckpointBytes5Output.ofK JFq_Weight07.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis07_00,basis07_01,basis07_02,basis07_03,basis07_04,basis07_05,basis07_06,basis07_07,basis07_08,basis07_09]
  change (0 : K)+ (1 : K)*scalar 980873277+ JHk_Rhs00.power*scalar 2043661226+ JHk_Rhs01.power*scalar 1477335533+ JHk_Rhs02.power*scalar 413519898+ JHk_Rhs03.power*scalar 1190379416+ JHk_Rhs04.power*scalar 1715324417+ JHk_Rhs05.power*scalar 1766783127+ JHk_Rhs06.power*scalar 1462315298+ JHk_Rhs07.power*scalar 1678604425+ JHk_Rhs08.power*scalar 275123297=⟨⟨1341902552,1006561559⟩,⟨887191166,402226612⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source07

theorem basis08_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 8=(995686286 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis08_00

theorem basis08_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 8=(1737116182 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis08_01

theorem basis08_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 8=(187108776 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis08_02

theorem basis08_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 8=(915137383 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis08_03

theorem basis08_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 8=(515754077 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis08_04

theorem basis08_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 8=(344497720 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis08_05

theorem basis08_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 8=(1909290949 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis08_06

theorem basis08_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 8=(1301456065 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis08_07

theorem basis08_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 8=(1616392957 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis08_08

theorem basis08_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 8=(1098591800 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis08_09

theorem source08 : totalAt 10 8=CheckpointBytes5Output.ofK JFq_Weight08.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis08_00,basis08_01,basis08_02,basis08_03,basis08_04,basis08_05,basis08_06,basis08_07,basis08_08,basis08_09]
  change (0 : K)+ (1 : K)*scalar 995686286+ JHk_Rhs00.power*scalar 1737116182+ JHk_Rhs01.power*scalar 187108776+ JHk_Rhs02.power*scalar 915137383+ JHk_Rhs03.power*scalar 515754077+ JHk_Rhs04.power*scalar 344497720+ JHk_Rhs05.power*scalar 1909290949+ JHk_Rhs06.power*scalar 1301456065+ JHk_Rhs07.power*scalar 1616392957+ JHk_Rhs08.power*scalar 1098591800=⟨⟨389252019,1335095117⟩,⟨699564237,1326781228⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source08

theorem basis09_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 9=(399117737 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis09_00

theorem basis09_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 9=(1901431938 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis09_01

theorem basis09_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 9=(472387532 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis09_02

theorem basis09_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 9=(1545697521 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis09_03

theorem basis09_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 9=(886937242 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis09_04

theorem basis09_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 9=(1978905789 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis09_05

theorem basis09_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 9=(401352768 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis09_06

theorem basis09_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 9=(146113973 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis09_07

theorem basis09_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 9=(1652943743 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis09_08

theorem basis09_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 9=(1623670490 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis09_09

theorem source09 : totalAt 10 9=CheckpointBytes5Output.ofK JFq_Weight09.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis09_00,basis09_01,basis09_02,basis09_03,basis09_04,basis09_05,basis09_06,basis09_07,basis09_08,basis09_09]
  change (0 : K)+ (1 : K)*scalar 399117737+ JHk_Rhs00.power*scalar 1901431938+ JHk_Rhs01.power*scalar 472387532+ JHk_Rhs02.power*scalar 1545697521+ JHk_Rhs03.power*scalar 886937242+ JHk_Rhs04.power*scalar 1978905789+ JHk_Rhs05.power*scalar 401352768+ JHk_Rhs06.power*scalar 146113973+ JHk_Rhs07.power*scalar 1652943743+ JHk_Rhs08.power*scalar 1623670490=⟨⟨1544585942,164414659⟩,⟨1447575431,1037421148⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source09

theorem basis10_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 10=(524063483 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis10_00

theorem basis10_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 10=(1031656046 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis10_01

theorem basis10_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 10=(993566271 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis10_02

theorem basis10_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 10=(1633839411 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis10_03

theorem basis10_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 10=(366566338 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis10_04

theorem basis10_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 10=(955507353 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis10_05

theorem basis10_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 10=(115766609 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis10_06

theorem basis10_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 10=(1640342497 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis10_07

theorem basis10_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 10=(2008748163 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis10_08

theorem basis10_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 10=(1370874809 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis10_09

theorem source10 : totalAt 10 10=CheckpointBytes5Output.ofK JFq_Weight10.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis10_00,basis10_01,basis10_02,basis10_03,basis10_04,basis10_05,basis10_06,basis10_07,basis10_08,basis10_09]
  change (0 : K)+ (1 : K)*scalar 524063483+ JHk_Rhs00.power*scalar 1031656046+ JHk_Rhs01.power*scalar 993566271+ JHk_Rhs02.power*scalar 1633839411+ JHk_Rhs03.power*scalar 366566338+ JHk_Rhs04.power*scalar 955507353+ JHk_Rhs05.power*scalar 115766609+ JHk_Rhs06.power*scalar 1640342497+ JHk_Rhs07.power*scalar 2008748163+ JHk_Rhs08.power*scalar 1370874809=⟨⟨2007177445,1478027531⟩,⟨543403815,1241504852⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source10
end AspisR1.JHl_Weight07_10
end
