import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_78_1 : poseidonExternalLinear s_78_0 = s_78_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_1
theorem round_78_2 : poseidonFullRound s_78_1 (poseidonExternalInitial 0) = s_78_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_2
theorem round_78_3 : poseidonFullRound s_78_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_78_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_3
theorem round_78_4 : poseidonFullRound s_78_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_78_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_4
theorem round_78_5 : poseidonFullRound s_78_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_78_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_5
theorem round_78_6 : poseidonInternalRound s_78_5 (poseidonInternalConstants 0) = s_78_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_6
theorem round_78_7 : poseidonInternalRound s_78_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_78_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_7
theorem round_78_8 : poseidonInternalRound s_78_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_78_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_8
theorem round_78_9 : poseidonInternalRound s_78_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_78_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_9
theorem round_78_10 : poseidonInternalRound s_78_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_78_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_10
theorem round_78_11 : poseidonInternalRound s_78_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_78_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_11
theorem round_78_12 : poseidonInternalRound s_78_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_78_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_12
theorem round_78_13 : poseidonInternalRound s_78_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_78_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_13
theorem round_78_14 : poseidonInternalRound s_78_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_78_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_14
theorem round_78_15 : poseidonInternalRound s_78_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_78_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_15
theorem round_78_16 : poseidonInternalRound s_78_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_78_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_16
theorem round_78_17 : poseidonInternalRound s_78_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_78_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_17
theorem round_78_18 : poseidonInternalRound s_78_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_78_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_18
theorem round_78_19 : poseidonInternalRound s_78_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_78_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_19
theorem round_78_20 : poseidonFullRound s_78_19 (poseidonExternalFinal 0) = s_78_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_20
theorem round_78_21 : poseidonFullRound s_78_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_78_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_21
theorem round_78_22 : poseidonFullRound s_78_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_78_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_22
theorem round_78_23 : poseidonFullRound s_78_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_78_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_78_23
theorem permutation_78 : poseidonPermutation s_78_0 = s_78_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_78_1,round_78_2,round_78_3,round_78_4,round_78_5,round_78_6,round_78_7,round_78_8,round_78_9,round_78_10,round_78_11,round_78_12,round_78_13,round_78_14,round_78_15,round_78_16,round_78_17,round_78_18,round_78_19,round_78_20,round_78_21,round_78_22,round_78_23]
#print axioms permutation_78
theorem node_78 : nodeCompress (![223002281,116293184,1618212914,1331700281,2109368512,559795428,204366681,229282374] : Fin 8 → Scalar) ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] = ![204734161,1001842950,1957867491,1426920886,531978693,466210636,1100375901,1136408495] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![223002281,116293184,1618212914,1331700281,2109368512,559795428,204366681,229282374] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_78_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_78]
  funext i
  fin_cases i <;> rfl
#print axioms node_78
end R1Z.PV_RunJoin_OutputModel16
