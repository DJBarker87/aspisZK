import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_11_1 : poseidonExternalLinear s_11_0 = s_11_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_1
theorem round_11_2 : poseidonFullRound s_11_1 (poseidonExternalInitial 0) = s_11_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_2
theorem round_11_3 : poseidonFullRound s_11_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_11_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_3
theorem round_11_4 : poseidonFullRound s_11_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_11_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_4
theorem round_11_5 : poseidonFullRound s_11_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_11_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_5
theorem round_11_6 : poseidonInternalRound s_11_5 (poseidonInternalConstants 0) = s_11_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_6
theorem round_11_7 : poseidonInternalRound s_11_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_11_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_7
theorem round_11_8 : poseidonInternalRound s_11_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_11_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_8
theorem round_11_9 : poseidonInternalRound s_11_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_11_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_9
theorem round_11_10 : poseidonInternalRound s_11_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_11_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_10
theorem round_11_11 : poseidonInternalRound s_11_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_11_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_11
theorem round_11_12 : poseidonInternalRound s_11_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_11_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_12
theorem round_11_13 : poseidonInternalRound s_11_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_11_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_13
theorem round_11_14 : poseidonInternalRound s_11_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_11_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_14
theorem round_11_15 : poseidonInternalRound s_11_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_11_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_15
theorem round_11_16 : poseidonInternalRound s_11_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_11_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_16
theorem round_11_17 : poseidonInternalRound s_11_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_11_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_17
theorem round_11_18 : poseidonInternalRound s_11_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_11_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_18
theorem round_11_19 : poseidonInternalRound s_11_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_11_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_19
theorem round_11_20 : poseidonFullRound s_11_19 (poseidonExternalFinal 0) = s_11_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_20
theorem round_11_21 : poseidonFullRound s_11_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_11_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_21
theorem round_11_22 : poseidonFullRound s_11_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_11_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_22
theorem round_11_23 : poseidonFullRound s_11_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_11_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_23
theorem permutation_11 : poseidonPermutation s_11_0 = s_11_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_11_1,round_11_2,round_11_3,round_11_4,round_11_5,round_11_6,round_11_7,round_11_8,round_11_9,round_11_10,round_11_11,round_11_12,round_11_13,round_11_14,round_11_15,round_11_16,round_11_17,round_11_18,round_11_19,round_11_20,round_11_21,round_11_22,round_11_23]
theorem node_11 : nodeCompress (![1180202183,1734852885,1208353062,189889914,943421826,507090805,389529953,896398700] : Fin 8 → Scalar) ![2081,2098,2115,2132,2149,2166,2183,2200] = ![439700881,730194574,1601626633,1478607356,953523754,1749099081,333248178,1763090787] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1180202183,1734852885,1208353062,189889914,943421826,507090805,389529953,896398700] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2081,2098,2115,2132,2149,2166,2183,2200] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2081,2098,2115,2132,2149,2166,2183,2200] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_11_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_11]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_11
#print axioms node_11
end R1Z.PV_RunJoin_PathModel16
