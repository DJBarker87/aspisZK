import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_79_1 : poseidonExternalLinear s_79_0 = s_79_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_1
theorem round_79_2 : poseidonFullRound s_79_1 (poseidonExternalInitial 0) = s_79_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_2
theorem round_79_3 : poseidonFullRound s_79_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_79_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_3
theorem round_79_4 : poseidonFullRound s_79_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_79_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_4
theorem round_79_5 : poseidonFullRound s_79_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_79_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_5
theorem round_79_6 : poseidonInternalRound s_79_5 (poseidonInternalConstants 0) = s_79_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_6
theorem round_79_7 : poseidonInternalRound s_79_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_79_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_7
theorem round_79_8 : poseidonInternalRound s_79_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_79_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_8
theorem round_79_9 : poseidonInternalRound s_79_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_79_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_9
theorem round_79_10 : poseidonInternalRound s_79_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_79_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_10
theorem round_79_11 : poseidonInternalRound s_79_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_79_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_11
theorem round_79_12 : poseidonInternalRound s_79_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_79_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_12
theorem round_79_13 : poseidonInternalRound s_79_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_79_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_13
theorem round_79_14 : poseidonInternalRound s_79_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_79_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_14
theorem round_79_15 : poseidonInternalRound s_79_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_79_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_15
theorem round_79_16 : poseidonInternalRound s_79_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_79_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_16
theorem round_79_17 : poseidonInternalRound s_79_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_79_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_17
theorem round_79_18 : poseidonInternalRound s_79_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_79_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_18
theorem round_79_19 : poseidonInternalRound s_79_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_79_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_19
theorem round_79_20 : poseidonFullRound s_79_19 (poseidonExternalFinal 0) = s_79_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_20
theorem round_79_21 : poseidonFullRound s_79_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_79_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_21
theorem round_79_22 : poseidonFullRound s_79_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_79_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_22
theorem round_79_23 : poseidonFullRound s_79_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_79_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_79_23
theorem permutation_79 : poseidonPermutation s_79_0 = s_79_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_79_1,round_79_2,round_79_3,round_79_4,round_79_5,round_79_6,round_79_7,round_79_8,round_79_9,round_79_10,round_79_11,round_79_12,round_79_13,round_79_14,round_79_15,round_79_16,round_79_17,round_79_18,round_79_19,round_79_20,round_79_21,round_79_22,round_79_23]
#print axioms permutation_79
theorem node_79 : nodeCompress (![204734161,1001842950,1957867491,1426920886,531978693,466210636,1100375901,1136408495] : Fin 8 → Scalar) ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] = ![1898472488,597255419,137386091,1805069421,1817944500,96708207,529143660,294781830] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![204734161,1001842950,1957867491,1426920886,531978693,466210636,1100375901,1136408495] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_79_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_79]
  funext i
  fin_cases i <;> rfl
#print axioms node_79
end R1Z.PV_RunJoin_OutputModel16
