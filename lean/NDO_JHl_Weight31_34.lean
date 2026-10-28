import NDO_JHl_WeightFormula
import RPt_JFq_Weights07
import RPt_JFq_Weights08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight31_34
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem basis31_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 31=(1832477516 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis31_00

theorem basis31_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 31=(826448985 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis31_01

theorem basis31_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 31=(1337576030 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis31_02

theorem basis31_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 31=(981401426 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis31_03

theorem basis31_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 31=(1497881927 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis31_04

theorem basis31_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 31=(2095250223 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis31_05

theorem basis31_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 31=(913082139 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis31_06

theorem basis31_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 31=(1541034938 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis31_07

theorem basis31_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 31=(578707264 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis31_08

theorem basis31_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 31=(110692438 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis31_09

theorem source31 : totalAt 10 31=CheckpointBytes5Output.ofK JFq_Weight31.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis31_00,basis31_01,basis31_02,basis31_03,basis31_04,basis31_05,basis31_06,basis31_07,basis31_08,basis31_09]
  change (0 : K)+ (1 : K)*scalar 1832477516+ JHk_Rhs00.power*scalar 826448985+ JHk_Rhs01.power*scalar 1337576030+ JHk_Rhs02.power*scalar 981401426+ JHk_Rhs03.power*scalar 1497881927+ JHk_Rhs04.power*scalar 2095250223+ JHk_Rhs05.power*scalar 913082139+ JHk_Rhs06.power*scalar 1541034938+ JHk_Rhs07.power*scalar 578707264+ JHk_Rhs08.power*scalar 110692438=⟨⟨1075414673,300392344⟩,⟨1382562915,168039541⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source31

theorem basis32_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 32=(1719134281 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis32_00

theorem basis32_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 32=(1095416042 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis32_01

theorem basis32_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 32=(2058568080 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis32_02

theorem basis32_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 32=(1653151249 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis32_03

theorem basis32_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 32=(228330423 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis32_04

theorem basis32_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 32=(1997885744 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis32_05

theorem basis32_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 32=(306425233 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis32_06

theorem basis32_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 32=(1576371696 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis32_07

theorem basis32_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 32=(1190468163 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis32_08

theorem basis32_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 32=(1657858136 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis32_09

theorem source32 : totalAt 10 32=CheckpointBytes5Output.ofK JFq_Weight32.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis32_00,basis32_01,basis32_02,basis32_03,basis32_04,basis32_05,basis32_06,basis32_07,basis32_08,basis32_09]
  change (0 : K)+ (1 : K)*scalar 1719134281+ JHk_Rhs00.power*scalar 1095416042+ JHk_Rhs01.power*scalar 2058568080+ JHk_Rhs02.power*scalar 1653151249+ JHk_Rhs03.power*scalar 228330423+ JHk_Rhs04.power*scalar 1997885744+ JHk_Rhs05.power*scalar 306425233+ JHk_Rhs06.power*scalar 1576371696+ JHk_Rhs07.power*scalar 1190468163+ JHk_Rhs08.power*scalar 1657858136=⟨⟨561396170,1339527674⟩,⟨1479423475,1743599567⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source32

theorem basis33_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 33=(1668214906 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis33_00

theorem basis33_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 33=(1195348773 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis33_01

theorem basis33_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 33=(2051179626 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis33_02

theorem basis33_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 33=(284618593 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis33_03

theorem basis33_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 33=(926128551 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis33_04

theorem basis33_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 33=(551104058 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis33_05

theorem basis33_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 33=(1165270983 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis33_06

theorem basis33_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 33=(124090758 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis33_07

theorem basis33_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 33=(175301470 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis33_08

theorem basis33_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 33=(1483020493 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis33_09

theorem source33 : totalAt 10 33=CheckpointBytes5Output.ofK JFq_Weight33.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis33_00,basis33_01,basis33_02,basis33_03,basis33_04,basis33_05,basis33_06,basis33_07,basis33_08,basis33_09]
  change (0 : K)+ (1 : K)*scalar 1668214906+ JHk_Rhs00.power*scalar 1195348773+ JHk_Rhs01.power*scalar 2051179626+ JHk_Rhs02.power*scalar 284618593+ JHk_Rhs03.power*scalar 926128551+ JHk_Rhs04.power*scalar 551104058+ JHk_Rhs05.power*scalar 1165270983+ JHk_Rhs06.power*scalar 124090758+ JHk_Rhs07.power*scalar 175301470+ JHk_Rhs08.power*scalar 1483020493=⟨⟨174205377,1445973176⟩,⟨102185487,2108320257⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source33

theorem basis34_00 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis00.node) 34=(1176831768 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis00.factor0,JHl_Basis00.factor1,JHl_Basis00.factor2,JHl_Basis00.factor3,JHl_Basis00.factor4,JHl_Basis00.factor5] <;> decide
#print axioms basis34_00

theorem basis34_01 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis01.node) 34=(2074681471 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis01.factor0,JHl_Basis01.factor1,JHl_Basis01.factor2,JHl_Basis01.factor3,JHl_Basis01.factor4,JHl_Basis01.factor5] <;> decide
#print axioms basis34_01

theorem basis34_02 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis02.node) 34=(1546770446 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis02.factor0,JHl_Basis02.factor1,JHl_Basis02.factor2,JHl_Basis02.factor3,JHl_Basis02.factor4,JHl_Basis02.factor5] <;> decide
#print axioms basis34_02

theorem basis34_03 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis03.node) 34=(1471505673 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis03.factor0,JHl_Basis03.factor1,JHl_Basis03.factor2,JHl_Basis03.factor3,JHl_Basis03.factor4,JHl_Basis03.factor5] <;> decide
#print axioms basis34_03

theorem basis34_04 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis04.node) 34=(1361130907 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis04.factor0,JHl_Basis04.factor1,JHl_Basis04.factor2,JHl_Basis04.factor3,JHl_Basis04.factor4,JHl_Basis04.factor5] <;> decide
#print axioms basis34_04

theorem basis34_05 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis05.node) 34=(1504563740 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis05.factor0,JHl_Basis05.factor1,JHl_Basis05.factor2,JHl_Basis05.factor3,JHl_Basis05.factor4,JHl_Basis05.factor5] <;> decide
#print axioms basis34_05

theorem basis34_06 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis06.node) 34=(1910388170 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis06.factor0,JHl_Basis06.factor1,JHl_Basis06.factor2,JHl_Basis06.factor3,JHl_Basis06.factor4,JHl_Basis06.factor5] <;> decide
#print axioms basis34_06

theorem basis34_07 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis07.node) 34=(177834866 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis07.factor0,JHl_Basis07.factor1,JHl_Basis07.factor2,JHl_Basis07.factor3,JHl_Basis07.factor4,JHl_Basis07.factor5] <;> decide
#print axioms basis34_07

theorem basis34_08 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis08.node) 34=(976640298 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis08.factor0,JHl_Basis08.factor1,JHl_Basis08.factor2,JHl_Basis08.factor3,JHl_Basis08.factor4,JHl_Basis08.factor5] <;> decide
#print axioms basis34_08

theorem basis34_09 : naturalLineValue (S7JoinBasisMachine.decode JHl_Basis09.node) 34=(860071560 : M31Exact) := by
  norm_num [naturalLineValue,Nat.bitIndices,JHl_Basis09.factor0,JHl_Basis09.factor1,JHl_Basis09.factor2,JHl_Basis09.factor3,JHl_Basis09.factor4,JHl_Basis09.factor5] <;> decide
#print axioms basis34_09

theorem source34 : totalAt 10 34=CheckpointBytes5Output.ofK JFq_Weight34.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,show (9 : Nat)<10 from by decide,dif_pos]
  rw [basis34_00,basis34_01,basis34_02,basis34_03,basis34_04,basis34_05,basis34_06,basis34_07,basis34_08,basis34_09]
  change (0 : K)+ (1 : K)*scalar 1176831768+ JHk_Rhs00.power*scalar 2074681471+ JHk_Rhs01.power*scalar 1546770446+ JHk_Rhs02.power*scalar 1471505673+ JHk_Rhs03.power*scalar 1361130907+ JHk_Rhs04.power*scalar 1504563740+ JHk_Rhs05.power*scalar 1910388170+ JHk_Rhs06.power*scalar 177834866+ JHk_Rhs07.power*scalar 976640298+ JHk_Rhs08.power*scalar 860071560=⟨⟨389194596,1667655162⟩,⟨1195923503,463827026⟩⟩
  unfold scalar JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source34
end AspisR1.JHl_Weight31_34
end
