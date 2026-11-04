import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_6_1 : poseidonExternalLinear s_6_0 = s_6_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_1
theorem round_6_2 : poseidonFullRound s_6_1 (poseidonExternalInitial 0) = s_6_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_2
theorem round_6_3 : poseidonFullRound s_6_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_6_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_3
theorem round_6_4 : poseidonFullRound s_6_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_6_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_4
theorem round_6_5 : poseidonFullRound s_6_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_6_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_5
theorem round_6_6 : poseidonInternalRound s_6_5 (poseidonInternalConstants 0) = s_6_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_6
theorem round_6_7 : poseidonInternalRound s_6_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_6_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_7
theorem round_6_8 : poseidonInternalRound s_6_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_6_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_8
theorem round_6_9 : poseidonInternalRound s_6_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_6_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_9
theorem round_6_10 : poseidonInternalRound s_6_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_6_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_10
theorem round_6_11 : poseidonInternalRound s_6_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_6_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_11
theorem round_6_12 : poseidonInternalRound s_6_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_6_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_12
theorem round_6_13 : poseidonInternalRound s_6_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_6_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_13
theorem round_6_14 : poseidonInternalRound s_6_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_6_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_14
theorem round_6_15 : poseidonInternalRound s_6_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_6_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_15
theorem round_6_16 : poseidonInternalRound s_6_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_6_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_16
theorem round_6_17 : poseidonInternalRound s_6_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_6_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_17
theorem round_6_18 : poseidonInternalRound s_6_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_6_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_18
theorem round_6_19 : poseidonInternalRound s_6_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_6_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_19
theorem round_6_20 : poseidonFullRound s_6_19 (poseidonExternalFinal 0) = s_6_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_20
theorem round_6_21 : poseidonFullRound s_6_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_6_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_21
theorem round_6_22 : poseidonFullRound s_6_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_6_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_22
theorem round_6_23 : poseidonFullRound s_6_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_6_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_6_23
theorem permutation_6 : poseidonPermutation s_6_0 = s_6_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_6_1,round_6_2,round_6_3,round_6_4,round_6_5,round_6_6,round_6_7,round_6_8,round_6_9,round_6_10,round_6_11,round_6_12,round_6_13,round_6_14,round_6_15,round_6_16,round_6_17,round_6_18,round_6_19,round_6_20,round_6_21,round_6_22,round_6_23]
theorem node_6 : nodeCompress (![2028667570,45893279,894642502,1930282162,1562116262,823639309,745717450,1034934647] : Fin 8 → Scalar) ![901,918,935,952,969,986,1003,1020] = ![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2028667570,45893279,894642502,1930282162,1562116262,823639309,745717450,1034934647] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![901,918,935,952,969,986,1003,1020] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![901,918,935,952,969,986,1003,1020] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_6_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_6]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_6
#print axioms node_6
end R1Z.PV_RunJoin_PathModel16
