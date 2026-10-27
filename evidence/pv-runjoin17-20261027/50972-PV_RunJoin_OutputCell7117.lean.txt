import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_71_1 : poseidonExternalLinear s_71_0 = s_71_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_1
theorem round_71_2 : poseidonFullRound s_71_1 (poseidonExternalInitial 0) = s_71_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_2
theorem round_71_3 : poseidonFullRound s_71_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_71_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_3
theorem round_71_4 : poseidonFullRound s_71_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_71_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_4
theorem round_71_5 : poseidonFullRound s_71_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_71_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_5
theorem round_71_6 : poseidonInternalRound s_71_5 (poseidonInternalConstants 0) = s_71_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_6
theorem round_71_7 : poseidonInternalRound s_71_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_71_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_7
theorem round_71_8 : poseidonInternalRound s_71_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_71_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_8
theorem round_71_9 : poseidonInternalRound s_71_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_71_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_9
theorem round_71_10 : poseidonInternalRound s_71_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_71_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_10
theorem round_71_11 : poseidonInternalRound s_71_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_71_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_11
theorem round_71_12 : poseidonInternalRound s_71_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_71_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_12
theorem round_71_13 : poseidonInternalRound s_71_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_71_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_13
theorem round_71_14 : poseidonInternalRound s_71_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_71_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_14
theorem round_71_15 : poseidonInternalRound s_71_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_71_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_15
theorem round_71_16 : poseidonInternalRound s_71_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_71_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_16
theorem round_71_17 : poseidonInternalRound s_71_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_71_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_17
theorem round_71_18 : poseidonInternalRound s_71_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_71_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_18
theorem round_71_19 : poseidonInternalRound s_71_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_71_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_19
theorem round_71_20 : poseidonFullRound s_71_19 (poseidonExternalFinal 0) = s_71_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_20
theorem round_71_21 : poseidonFullRound s_71_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_71_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_21
theorem round_71_22 : poseidonFullRound s_71_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_71_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_22
theorem round_71_23 : poseidonFullRound s_71_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_71_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_71_23
theorem permutation_71 : poseidonPermutation s_71_0 = s_71_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_71_1,round_71_2,round_71_3,round_71_4,round_71_5,round_71_6,round_71_7,round_71_8,round_71_9,round_71_10,round_71_11,round_71_12,round_71_13,round_71_14,round_71_15,round_71_16,round_71_17,round_71_18,round_71_19,round_71_20,round_71_21,round_71_22,round_71_23]
#print axioms permutation_71
theorem node_71 : nodeCompress (![1107000820,1338554320,488374647,453509918,222991326,1075792838,352883826,459345458] : Fin 8 → Scalar) ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] = ![2130322641,1665426257,1206815286,1635654730,225199437,982012671,514446081,115798455] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1107000820,1338554320,488374647,453509918,222991326,1075792838,352883826,459345458] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_71_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_71]
  funext i
  fin_cases i <;> rfl
#print axioms node_71
end R1Z.PV_RunJoin_OutputModel16
