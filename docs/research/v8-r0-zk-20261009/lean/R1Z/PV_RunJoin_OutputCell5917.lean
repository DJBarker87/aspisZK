import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_59_1 : poseidonExternalLinear s_59_0 = s_59_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_1
theorem round_59_2 : poseidonFullRound s_59_1 (poseidonExternalInitial 0) = s_59_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_2
theorem round_59_3 : poseidonFullRound s_59_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_59_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_3
theorem round_59_4 : poseidonFullRound s_59_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_59_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_4
theorem round_59_5 : poseidonFullRound s_59_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_59_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_5
theorem round_59_6 : poseidonInternalRound s_59_5 (poseidonInternalConstants 0) = s_59_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_6
theorem round_59_7 : poseidonInternalRound s_59_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_59_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_7
theorem round_59_8 : poseidonInternalRound s_59_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_59_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_8
theorem round_59_9 : poseidonInternalRound s_59_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_59_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_9
theorem round_59_10 : poseidonInternalRound s_59_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_59_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_10
theorem round_59_11 : poseidonInternalRound s_59_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_59_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_11
theorem round_59_12 : poseidonInternalRound s_59_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_59_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_12
theorem round_59_13 : poseidonInternalRound s_59_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_59_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_13
theorem round_59_14 : poseidonInternalRound s_59_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_59_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_14
theorem round_59_15 : poseidonInternalRound s_59_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_59_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_15
theorem round_59_16 : poseidonInternalRound s_59_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_59_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_16
theorem round_59_17 : poseidonInternalRound s_59_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_59_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_17
theorem round_59_18 : poseidonInternalRound s_59_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_59_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_18
theorem round_59_19 : poseidonInternalRound s_59_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_59_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_19
theorem round_59_20 : poseidonFullRound s_59_19 (poseidonExternalFinal 0) = s_59_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_20
theorem round_59_21 : poseidonFullRound s_59_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_59_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_21
theorem round_59_22 : poseidonFullRound s_59_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_59_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_22
theorem round_59_23 : poseidonFullRound s_59_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_59_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_59_23
theorem permutation_59 : poseidonPermutation s_59_0 = s_59_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_59_1,round_59_2,round_59_3,round_59_4,round_59_5,round_59_6,round_59_7,round_59_8,round_59_9,round_59_10,round_59_11,round_59_12,round_59_13,round_59_14,round_59_15,round_59_16,round_59_17,round_59_18,round_59_19,round_59_20,round_59_21,round_59_22,round_59_23]
#print axioms permutation_59
theorem node_59 : nodeCompress (![1660714618,58624303,617770228,599383446,771361068,1834589194,51322319,276611708] : Fin 8 → Scalar) ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] = ![1186265903,415151008,1902434632,1450931092,922955725,1977809658,160284130,1987330095] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1660714618,58624303,617770228,599383446,771361068,1834589194,51322319,276611708] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_59_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_59]
  funext i
  fin_cases i <;> rfl
#print axioms node_59
end R1Z.PV_RunJoin_OutputModel16
