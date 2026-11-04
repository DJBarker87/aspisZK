import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_21_1 : poseidonExternalLinear s_21_0 = s_21_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_1
theorem round_21_2 : poseidonFullRound s_21_1 (poseidonExternalInitial 0) = s_21_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_2
theorem round_21_3 : poseidonFullRound s_21_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_21_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_3
theorem round_21_4 : poseidonFullRound s_21_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_21_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_4
theorem round_21_5 : poseidonFullRound s_21_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_21_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_5
theorem round_21_6 : poseidonInternalRound s_21_5 (poseidonInternalConstants 0) = s_21_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_6
theorem round_21_7 : poseidonInternalRound s_21_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_21_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_7
theorem round_21_8 : poseidonInternalRound s_21_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_21_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_8
theorem round_21_9 : poseidonInternalRound s_21_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_21_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_9
theorem round_21_10 : poseidonInternalRound s_21_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_21_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_10
theorem round_21_11 : poseidonInternalRound s_21_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_21_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_11
theorem round_21_12 : poseidonInternalRound s_21_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_21_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_12
theorem round_21_13 : poseidonInternalRound s_21_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_21_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_13
theorem round_21_14 : poseidonInternalRound s_21_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_21_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_14
theorem round_21_15 : poseidonInternalRound s_21_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_21_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_15
theorem round_21_16 : poseidonInternalRound s_21_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_21_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_16
theorem round_21_17 : poseidonInternalRound s_21_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_21_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_17
theorem round_21_18 : poseidonInternalRound s_21_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_21_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_18
theorem round_21_19 : poseidonInternalRound s_21_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_21_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_19
theorem round_21_20 : poseidonFullRound s_21_19 (poseidonExternalFinal 0) = s_21_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_20
theorem round_21_21 : poseidonFullRound s_21_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_21_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_21
theorem round_21_22 : poseidonFullRound s_21_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_21_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_22
theorem round_21_23 : poseidonFullRound s_21_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_21_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_21_23
theorem permutation_21 : poseidonPermutation s_21_0 = s_21_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_21_1,round_21_2,round_21_3,round_21_4,round_21_5,round_21_6,round_21_7,round_21_8,round_21_9,round_21_10,round_21_11,round_21_12,round_21_13,round_21_14,round_21_15,round_21_16,round_21_17,round_21_18,round_21_19,round_21_20,round_21_21,round_21_22,round_21_23]
theorem node_21 : nodeCompress (![2281,2298,2315,2332,2349,2366,2383,2400] : Fin 8 → Scalar) ![493855764,1737005017,1044011334,780794261,292608247,1805935865,972083531,346637554] = ![516145591,463254876,1878652377,174797573,1017414220,839141147,732445005,1267400728] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2281,2298,2315,2332,2349,2366,2383,2400] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![493855764,1737005017,1044011334,780794261,292608247,1805935865,972083531,346637554] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![493855764,1737005017,1044011334,780794261,292608247,1805935865,972083531,346637554] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_21_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_21]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_21
#print axioms node_21
end R1Z.PV_RunJoin_PathModel16
