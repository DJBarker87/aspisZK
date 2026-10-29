import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_28_1 : poseidonExternalLinear s_28_0 = s_28_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_1
theorem round_28_2 : poseidonFullRound s_28_1 (poseidonExternalInitial 0) = s_28_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_2
theorem round_28_3 : poseidonFullRound s_28_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_28_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_3
theorem round_28_4 : poseidonFullRound s_28_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_28_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_4
theorem round_28_5 : poseidonFullRound s_28_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_28_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_5
theorem round_28_6 : poseidonInternalRound s_28_5 (poseidonInternalConstants 0) = s_28_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_6
theorem round_28_7 : poseidonInternalRound s_28_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_28_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_7
theorem round_28_8 : poseidonInternalRound s_28_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_28_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_8
theorem round_28_9 : poseidonInternalRound s_28_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_28_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_9
theorem round_28_10 : poseidonInternalRound s_28_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_28_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_10
theorem round_28_11 : poseidonInternalRound s_28_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_28_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_11
theorem round_28_12 : poseidonInternalRound s_28_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_28_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_12
theorem round_28_13 : poseidonInternalRound s_28_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_28_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_13
theorem round_28_14 : poseidonInternalRound s_28_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_28_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_14
theorem round_28_15 : poseidonInternalRound s_28_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_28_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_15
theorem round_28_16 : poseidonInternalRound s_28_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_28_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_16
theorem round_28_17 : poseidonInternalRound s_28_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_28_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_17
theorem round_28_18 : poseidonInternalRound s_28_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_28_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_18
theorem round_28_19 : poseidonInternalRound s_28_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_28_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_19
theorem round_28_20 : poseidonFullRound s_28_19 (poseidonExternalFinal 0) = s_28_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_20
theorem round_28_21 : poseidonFullRound s_28_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_28_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_21
theorem round_28_22 : poseidonFullRound s_28_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_28_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_22
theorem round_28_23 : poseidonFullRound s_28_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_28_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_28_23
theorem permutation_28 : poseidonPermutation s_28_0 = s_28_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_28_1,round_28_2,round_28_3,round_28_4,round_28_5,round_28_6,round_28_7,round_28_8,round_28_9,round_28_10,round_28_11,round_28_12,round_28_13,round_28_14,round_28_15,round_28_16,round_28_17,round_28_18,round_28_19,round_28_20,round_28_21,round_28_22,round_28_23]
theorem node_28 : nodeCompress (![1542818520,1882037664,1251951877,1554108809,81746851,159927545,2111428769,132405182] : Fin 8 → Scalar) ![3101,3118,3135,3152,3169,3186,3203,3220] = ![407525056,1458948676,1930040251,1044760048,961029422,441494278,1982425121,1368876468] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1542818520,1882037664,1251951877,1554108809,81746851,159927545,2111428769,132405182] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![3101,3118,3135,3152,3169,3186,3203,3220] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![3101,3118,3135,3152,3169,3186,3203,3220] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_28_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_28]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_28
#print axioms node_28
end R1Z.PV_RunJoin_PathModel16
