import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_54_1 : poseidonExternalLinear s_54_0 = s_54_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_1
theorem round_54_2 : poseidonFullRound s_54_1 (poseidonExternalInitial 0) = s_54_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_2
theorem round_54_3 : poseidonFullRound s_54_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_54_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_3
theorem round_54_4 : poseidonFullRound s_54_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_54_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_4
theorem round_54_5 : poseidonFullRound s_54_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_54_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_5
theorem round_54_6 : poseidonInternalRound s_54_5 (poseidonInternalConstants 0) = s_54_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_6
theorem round_54_7 : poseidonInternalRound s_54_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_54_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_7
theorem round_54_8 : poseidonInternalRound s_54_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_54_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_8
theorem round_54_9 : poseidonInternalRound s_54_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_54_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_9
theorem round_54_10 : poseidonInternalRound s_54_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_54_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_10
theorem round_54_11 : poseidonInternalRound s_54_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_54_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_11
theorem round_54_12 : poseidonInternalRound s_54_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_54_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_12
theorem round_54_13 : poseidonInternalRound s_54_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_54_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_13
theorem round_54_14 : poseidonInternalRound s_54_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_54_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_14
theorem round_54_15 : poseidonInternalRound s_54_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_54_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_15
theorem round_54_16 : poseidonInternalRound s_54_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_54_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_16
theorem round_54_17 : poseidonInternalRound s_54_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_54_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_17
theorem round_54_18 : poseidonInternalRound s_54_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_54_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_18
theorem round_54_19 : poseidonInternalRound s_54_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_54_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_19
theorem round_54_20 : poseidonFullRound s_54_19 (poseidonExternalFinal 0) = s_54_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_20
theorem round_54_21 : poseidonFullRound s_54_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_54_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_21
theorem round_54_22 : poseidonFullRound s_54_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_54_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_22
theorem round_54_23 : poseidonFullRound s_54_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_54_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_54_23
theorem permutation_54 : poseidonPermutation s_54_0 = s_54_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_54_1,round_54_2,round_54_3,round_54_4,round_54_5,round_54_6,round_54_7,round_54_8,round_54_9,round_54_10,round_54_11,round_54_12,round_54_13,round_54_14,round_54_15,round_54_16,round_54_17,round_54_18,round_54_19,round_54_20,round_54_21,round_54_22,round_54_23]
#print axioms permutation_54
theorem node_54 : nodeCompress (![1310587138,1547028228,724201667,460418645,1935078033,56710135,329156384,480377036] : Fin 8 → Scalar) ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] = ![126701447,2048228689,1569040746,816942090,934340682,707737539,1640113194,1531834504] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1310587138,1547028228,724201667,460418645,1935078033,56710135,329156384,480377036] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_54_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_54]
  funext i
  fin_cases i <;> rfl
#print axioms node_54
end R1Z.PV_RunJoin_OutputModel16
