import NDO_JHl_WeightFormula
import RPt_JFq_Weights12
import RPt_JFq_Weights13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight51_54
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis51_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 51=(1197418799 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis51_00

theorem basis51_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 51=(1142114463 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis51_01

theorem basis51_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 51=(1699144795 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis51_02

theorem basis51_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 51=(1478857084 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis51_03

theorem basis51_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 51=(1012239734 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis51_04

theorem basis51_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 51=(897626913 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis51_05

theorem basis51_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 51=(93201568 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis51_06

theorem basis51_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 51=(1989288261 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis51_07

theorem basis51_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 51=(967129913 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis51_08

theorem basis51_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 51=(1913408778 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis51_09

theorem source51 : totalAt 10 51=CheckpointBytes5Output.ofK JFq_Weight51.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis51_00,basis51_01,basis51_02,basis51_03,basis51_04,basis51_05,basis51_06,basis51_07,basis51_08,basis51_09]
  change (0 : K)+ (1 : K)*scalar 1197418799+ JHk_Rhs00.power*scalar 1142114463+ JHk_Rhs01.power*scalar 1699144795+ JHk_Rhs02.power*scalar 1478857084+ JHk_Rhs03.power*scalar 1012239734+ JHk_Rhs04.power*scalar 897626913+ JHk_Rhs05.power*scalar 93201568+ JHk_Rhs06.power*scalar 1989288261+ JHk_Rhs07.power*scalar 967129913+ JHk_Rhs08.power*scalar 1913408778=⟨⟨2126728145,213200088⟩,⟨896531941,1321745178⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source51

theorem basis52_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 52=(1545026243 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis52_00

theorem basis52_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 52=(893542961 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis52_01

theorem basis52_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 52=(1347413011 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis52_02

theorem basis52_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 52=(850277277 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis52_03

theorem basis52_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 52=(1829563098 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis52_04

theorem basis52_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 52=(447578063 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis52_05

theorem basis52_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 52=(931585373 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis52_06

theorem basis52_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 52=(1475216440 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis52_07

theorem basis52_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 52=(2038357073 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis52_08

theorem basis52_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 52=(921129735 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis52_09

theorem source52 : totalAt 10 52=CheckpointBytes5Output.ofK JFq_Weight52.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis52_00,basis52_01,basis52_02,basis52_03,basis52_04,basis52_05,basis52_06,basis52_07,basis52_08,basis52_09]
  change (0 : K)+ (1 : K)*scalar 1545026243+ JHk_Rhs00.power*scalar 893542961+ JHk_Rhs01.power*scalar 1347413011+ JHk_Rhs02.power*scalar 850277277+ JHk_Rhs03.power*scalar 1829563098+ JHk_Rhs04.power*scalar 447578063+ JHk_Rhs05.power*scalar 931585373+ JHk_Rhs06.power*scalar 1475216440+ JHk_Rhs07.power*scalar 2038357073+ JHk_Rhs08.power*scalar 921129735=⟨⟨1778388959,757436448⟩,⟨1589763598,1955873460⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source52

theorem basis53_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 53=(942962948 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis53_00

theorem basis53_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 53=(271989019 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis53_01

theorem basis53_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 53=(1241271996 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis53_02

theorem basis53_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 53=(24378630 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis53_03

theorem basis53_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 53=(1177143979 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis53_04

theorem basis53_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 53=(1998092615 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis53_05

theorem basis53_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 53=(1955848441 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis53_06

theorem basis53_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 53=(1173879173 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis53_07

theorem basis53_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 53=(1967403849 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis53_08

theorem basis53_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 53=(1199649640 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis53_09

theorem source53 : totalAt 10 53=CheckpointBytes5Output.ofK JFq_Weight53.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis53_00,basis53_01,basis53_02,basis53_03,basis53_04,basis53_05,basis53_06,basis53_07,basis53_08,basis53_09]
  change (0 : K)+ (1 : K)*scalar 942962948+ JHk_Rhs00.power*scalar 271989019+ JHk_Rhs01.power*scalar 1241271996+ JHk_Rhs02.power*scalar 24378630+ JHk_Rhs03.power*scalar 1177143979+ JHk_Rhs04.power*scalar 1998092615+ JHk_Rhs05.power*scalar 1955848441+ JHk_Rhs06.power*scalar 1173879173+ JHk_Rhs07.power*scalar 1967403849+ JHk_Rhs08.power*scalar 1199649640=⟨⟨491670158,1890964609⟩,⟨2035659000,544890737⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source53

theorem basis54_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 54=(727534964 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis54_00

theorem basis54_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 54=(1711364084 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis54_01

theorem basis54_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 54=(2042528338 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis54_02

theorem basis54_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 54=(1198895506 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis54_03

theorem basis54_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 54=(692976692 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis54_04

theorem basis54_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 54=(465633717 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis54_05

theorem basis54_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 54=(539456788 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis54_06

theorem basis54_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 54=(1935025423 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis54_07

theorem basis54_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 54=(1804795748 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis54_08

theorem basis54_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 54=(1138755976 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis54_09

theorem source54 : totalAt 10 54=CheckpointBytes5Output.ofK JFq_Weight54.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis54_00,basis54_01,basis54_02,basis54_03,basis54_04,basis54_05,basis54_06,basis54_07,basis54_08,basis54_09]
  change (0 : K)+ (1 : K)*scalar 727534964+ JHk_Rhs00.power*scalar 1711364084+ JHk_Rhs01.power*scalar 2042528338+ JHk_Rhs02.power*scalar 1198895506+ JHk_Rhs03.power*scalar 692976692+ JHk_Rhs04.power*scalar 465633717+ JHk_Rhs05.power*scalar 539456788+ JHk_Rhs06.power*scalar 1935025423+ JHk_Rhs07.power*scalar 1804795748+ JHk_Rhs08.power*scalar 1138755976=⟨⟨1740694871,192126017⟩,⟨43512142,1005157139⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source54
end AspisR1.JHl_Weight51_54
end
