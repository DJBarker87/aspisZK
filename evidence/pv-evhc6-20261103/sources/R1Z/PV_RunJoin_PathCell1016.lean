import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_10_1 : poseidonExternalLinear s_10_0 = s_10_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_1
theorem round_10_2 : poseidonFullRound s_10_1 (poseidonExternalInitial 0) = s_10_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_2
theorem round_10_3 : poseidonFullRound s_10_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_10_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_3
theorem round_10_4 : poseidonFullRound s_10_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_10_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_4
theorem round_10_5 : poseidonFullRound s_10_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_10_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_5
theorem round_10_6 : poseidonInternalRound s_10_5 (poseidonInternalConstants 0) = s_10_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_6
theorem round_10_7 : poseidonInternalRound s_10_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_10_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_7
theorem round_10_8 : poseidonInternalRound s_10_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_10_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_8
theorem round_10_9 : poseidonInternalRound s_10_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_10_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_9
theorem round_10_10 : poseidonInternalRound s_10_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_10_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_10
theorem round_10_11 : poseidonInternalRound s_10_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_10_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_11
theorem round_10_12 : poseidonInternalRound s_10_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_10_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_12
theorem round_10_13 : poseidonInternalRound s_10_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_10_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_13
theorem round_10_14 : poseidonInternalRound s_10_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_10_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_14
theorem round_10_15 : poseidonInternalRound s_10_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_10_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_15
theorem round_10_16 : poseidonInternalRound s_10_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_10_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_16
theorem round_10_17 : poseidonInternalRound s_10_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_10_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_17
theorem round_10_18 : poseidonInternalRound s_10_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_10_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_18
theorem round_10_19 : poseidonInternalRound s_10_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_10_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_19
theorem round_10_20 : poseidonFullRound s_10_19 (poseidonExternalFinal 0) = s_10_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_20
theorem round_10_21 : poseidonFullRound s_10_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_10_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_21
theorem round_10_22 : poseidonFullRound s_10_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_10_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_22
theorem round_10_23 : poseidonFullRound s_10_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_10_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_23
theorem permutation_10 : poseidonPermutation s_10_0 = s_10_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_10_1,round_10_2,round_10_3,round_10_4,round_10_5,round_10_6,round_10_7,round_10_8,round_10_9,round_10_10,round_10_11,round_10_12,round_10_13,round_10_14,round_10_15,round_10_16,round_10_17,round_10_18,round_10_19,round_10_20,round_10_21,round_10_22,round_10_23]
theorem node_10 : nodeCompress (![600625215,237354909,439972622,263907834,1075778621,569932161,1744169643,1373371366] : Fin 8 → Scalar) ![2061,2078,2095,2112,2129,2146,2163,2180] = ![1180202183,1734852885,1208353062,189889914,943421826,507090805,389529953,896398700] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![600625215,237354909,439972622,263907834,1075778621,569932161,1744169643,1373371366] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2061,2078,2095,2112,2129,2146,2163,2180] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2061,2078,2095,2112,2129,2146,2163,2180] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_10_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_10]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_10
#print axioms node_10
end R1Z.PV_RunJoin_PathModel16
