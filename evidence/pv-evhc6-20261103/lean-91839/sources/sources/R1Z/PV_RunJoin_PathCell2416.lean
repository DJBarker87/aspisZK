import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_24_1 : poseidonExternalLinear s_24_0 = s_24_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_1
theorem round_24_2 : poseidonFullRound s_24_1 (poseidonExternalInitial 0) = s_24_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_2
theorem round_24_3 : poseidonFullRound s_24_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_24_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_3
theorem round_24_4 : poseidonFullRound s_24_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_24_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_4
theorem round_24_5 : poseidonFullRound s_24_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_24_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_5
theorem round_24_6 : poseidonInternalRound s_24_5 (poseidonInternalConstants 0) = s_24_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_6
theorem round_24_7 : poseidonInternalRound s_24_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_24_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_7
theorem round_24_8 : poseidonInternalRound s_24_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_24_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_8
theorem round_24_9 : poseidonInternalRound s_24_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_24_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_9
theorem round_24_10 : poseidonInternalRound s_24_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_24_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_10
theorem round_24_11 : poseidonInternalRound s_24_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_24_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_11
theorem round_24_12 : poseidonInternalRound s_24_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_24_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_12
theorem round_24_13 : poseidonInternalRound s_24_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_24_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_13
theorem round_24_14 : poseidonInternalRound s_24_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_24_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_14
theorem round_24_15 : poseidonInternalRound s_24_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_24_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_15
theorem round_24_16 : poseidonInternalRound s_24_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_24_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_16
theorem round_24_17 : poseidonInternalRound s_24_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_24_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_17
theorem round_24_18 : poseidonInternalRound s_24_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_24_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_18
theorem round_24_19 : poseidonInternalRound s_24_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_24_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_19
theorem round_24_20 : poseidonFullRound s_24_19 (poseidonExternalFinal 0) = s_24_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_20
theorem round_24_21 : poseidonFullRound s_24_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_24_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_21
theorem round_24_22 : poseidonFullRound s_24_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_24_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_22
theorem round_24_23 : poseidonFullRound s_24_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_24_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_24_23
theorem permutation_24 : poseidonPermutation s_24_0 = s_24_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_24_1,round_24_2,round_24_3,round_24_4,round_24_5,round_24_6,round_24_7,round_24_8,round_24_9,round_24_10,round_24_11,round_24_12,round_24_13,round_24_14,round_24_15,round_24_16,round_24_17,round_24_18,round_24_19,round_24_20,round_24_21,round_24_22,round_24_23]
theorem node_24 : nodeCompress (![2136837586,679543585,225002526,1101048270,2134488188,1020968422,1342497638,1907691591] : Fin 8 → Scalar) ![2341,2358,2375,2392,2409,2426,2443,2460] = ![2081739590,582598927,447833412,1551242300,10472096,1276966930,111682118,132339882] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2136837586,679543585,225002526,1101048270,2134488188,1020968422,1342497638,1907691591] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2341,2358,2375,2392,2409,2426,2443,2460] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2341,2358,2375,2392,2409,2426,2443,2460] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_24_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_24]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_24
#print axioms node_24
end R1Z.PV_RunJoin_PathModel16
