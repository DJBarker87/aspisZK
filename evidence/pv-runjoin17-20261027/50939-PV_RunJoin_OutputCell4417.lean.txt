import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_44_1 : poseidonExternalLinear s_44_0 = s_44_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_1
theorem round_44_2 : poseidonFullRound s_44_1 (poseidonExternalInitial 0) = s_44_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_2
theorem round_44_3 : poseidonFullRound s_44_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_44_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_3
theorem round_44_4 : poseidonFullRound s_44_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_44_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_4
theorem round_44_5 : poseidonFullRound s_44_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_44_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_5
theorem round_44_6 : poseidonInternalRound s_44_5 (poseidonInternalConstants 0) = s_44_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_6
theorem round_44_7 : poseidonInternalRound s_44_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_44_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_7
theorem round_44_8 : poseidonInternalRound s_44_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_44_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_8
theorem round_44_9 : poseidonInternalRound s_44_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_44_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_9
theorem round_44_10 : poseidonInternalRound s_44_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_44_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_10
theorem round_44_11 : poseidonInternalRound s_44_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_44_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_11
theorem round_44_12 : poseidonInternalRound s_44_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_44_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_12
theorem round_44_13 : poseidonInternalRound s_44_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_44_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_13
theorem round_44_14 : poseidonInternalRound s_44_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_44_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_14
theorem round_44_15 : poseidonInternalRound s_44_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_44_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_15
theorem round_44_16 : poseidonInternalRound s_44_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_44_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_16
theorem round_44_17 : poseidonInternalRound s_44_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_44_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_17
theorem round_44_18 : poseidonInternalRound s_44_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_44_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_18
theorem round_44_19 : poseidonInternalRound s_44_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_44_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_19
theorem round_44_20 : poseidonFullRound s_44_19 (poseidonExternalFinal 0) = s_44_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_20
theorem round_44_21 : poseidonFullRound s_44_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_44_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_21
theorem round_44_22 : poseidonFullRound s_44_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_44_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_22
theorem round_44_23 : poseidonFullRound s_44_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_44_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_44_23
theorem permutation_44 : poseidonPermutation s_44_0 = s_44_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_44_1,round_44_2,round_44_3,round_44_4,round_44_5,round_44_6,round_44_7,round_44_8,round_44_9,round_44_10,round_44_11,round_44_12,round_44_13,round_44_14,round_44_15,round_44_16,round_44_17,round_44_18,round_44_19,round_44_20,round_44_21,round_44_22,round_44_23]
#print axioms permutation_44
theorem node_44 : nodeCompress (![1061398933,509112012,1799578086,482877258,2025164722,672733548,359961336,1470147015] : Fin 8 → Scalar) ![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] = ![650311058,434968666,41653783,849815005,1944690526,1561873308,545397838,336751789] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1061398933,509112012,1799578086,482877258,2025164722,672733548,359961336,1470147015] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_44_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_44]
  funext i
  fin_cases i <;> rfl
#print axioms node_44
end R1Z.PV_RunJoin_OutputModel16
