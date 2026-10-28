import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_12_1 : poseidonExternalLinear s_12_0 = s_12_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_1
theorem round_12_2 : poseidonFullRound s_12_1 (poseidonExternalInitial 0) = s_12_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_2
theorem round_12_3 : poseidonFullRound s_12_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_12_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_3
theorem round_12_4 : poseidonFullRound s_12_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_12_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_4
theorem round_12_5 : poseidonFullRound s_12_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_12_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_5
theorem round_12_6 : poseidonInternalRound s_12_5 (poseidonInternalConstants 0) = s_12_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_6
theorem round_12_7 : poseidonInternalRound s_12_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_12_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_7
theorem round_12_8 : poseidonInternalRound s_12_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_12_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_8
theorem round_12_9 : poseidonInternalRound s_12_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_12_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_9
theorem round_12_10 : poseidonInternalRound s_12_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_12_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_10
theorem round_12_11 : poseidonInternalRound s_12_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_12_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_11
theorem round_12_12 : poseidonInternalRound s_12_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_12_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_12
theorem round_12_13 : poseidonInternalRound s_12_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_12_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_13
theorem round_12_14 : poseidonInternalRound s_12_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_12_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_14
theorem round_12_15 : poseidonInternalRound s_12_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_12_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_15
theorem round_12_16 : poseidonInternalRound s_12_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_12_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_16
theorem round_12_17 : poseidonInternalRound s_12_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_12_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_17
theorem round_12_18 : poseidonInternalRound s_12_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_12_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_18
theorem round_12_19 : poseidonInternalRound s_12_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_12_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_19
theorem round_12_20 : poseidonFullRound s_12_19 (poseidonExternalFinal 0) = s_12_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_20
theorem round_12_21 : poseidonFullRound s_12_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_12_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_21
theorem round_12_22 : poseidonFullRound s_12_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_12_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_22
theorem round_12_23 : poseidonFullRound s_12_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_12_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_23
theorem permutation_12 : poseidonPermutation s_12_0 = s_12_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_12_1,round_12_2,round_12_3,round_12_4,round_12_5,round_12_6,round_12_7,round_12_8,round_12_9,round_12_10,round_12_11,round_12_12,round_12_13,round_12_14,round_12_15,round_12_16,round_12_17,round_12_18,round_12_19,round_12_20,round_12_21,round_12_22,round_12_23]
theorem node_12 : nodeCompress (![2101,2118,2135,2152,2169,2186,2203,2220] : Fin 8 → Scalar) ![439700881,730194574,1601626633,1478607356,953523754,1749099081,333248178,1763090787] = ![891777458,519287294,1981395871,1193798350,1897410699,1175699129,1224545956,757035799] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2101,2118,2135,2152,2169,2186,2203,2220] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![439700881,730194574,1601626633,1478607356,953523754,1749099081,333248178,1763090787] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![439700881,730194574,1601626633,1478607356,953523754,1749099081,333248178,1763090787] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_12_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_12]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_12
#print axioms node_12
end R1Z.PV_RunJoin_PathModel16
