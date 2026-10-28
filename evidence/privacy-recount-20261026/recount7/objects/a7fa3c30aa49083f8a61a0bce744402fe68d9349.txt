import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_70_1 : poseidonExternalLinear s_70_0 = s_70_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_1
theorem round_70_2 : poseidonFullRound s_70_1 (poseidonExternalInitial 0) = s_70_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_2
theorem round_70_3 : poseidonFullRound s_70_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_70_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_3
theorem round_70_4 : poseidonFullRound s_70_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_70_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_4
theorem round_70_5 : poseidonFullRound s_70_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_70_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_5
theorem round_70_6 : poseidonInternalRound s_70_5 (poseidonInternalConstants 0) = s_70_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_6
theorem round_70_7 : poseidonInternalRound s_70_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_70_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_7
theorem round_70_8 : poseidonInternalRound s_70_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_70_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_8
theorem round_70_9 : poseidonInternalRound s_70_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_70_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_9
theorem round_70_10 : poseidonInternalRound s_70_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_70_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_10
theorem round_70_11 : poseidonInternalRound s_70_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_70_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_11
theorem round_70_12 : poseidonInternalRound s_70_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_70_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_12
theorem round_70_13 : poseidonInternalRound s_70_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_70_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_13
theorem round_70_14 : poseidonInternalRound s_70_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_70_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_14
theorem round_70_15 : poseidonInternalRound s_70_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_70_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_15
theorem round_70_16 : poseidonInternalRound s_70_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_70_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_16
theorem round_70_17 : poseidonInternalRound s_70_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_70_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_17
theorem round_70_18 : poseidonInternalRound s_70_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_70_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_18
theorem round_70_19 : poseidonInternalRound s_70_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_70_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_19
theorem round_70_20 : poseidonFullRound s_70_19 (poseidonExternalFinal 0) = s_70_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_20
theorem round_70_21 : poseidonFullRound s_70_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_70_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_21
theorem round_70_22 : poseidonFullRound s_70_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_70_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_22
theorem round_70_23 : poseidonFullRound s_70_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_70_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_70_23
theorem permutation_70 : poseidonPermutation s_70_0 = s_70_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_70_1,round_70_2,round_70_3,round_70_4,round_70_5,round_70_6,round_70_7,round_70_8,round_70_9,round_70_10,round_70_11,round_70_12,round_70_13,round_70_14,round_70_15,round_70_16,round_70_17,round_70_18,round_70_19,round_70_20,round_70_21,round_70_22,round_70_23]
#print axioms permutation_70
theorem node_70 : nodeCompress (![2054510981,1825804774,418288139,378397545,1185114525,81172068,361707637,1111542572] : Fin 8 → Scalar) ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] = ![1107000820,1338554320,488374647,453509918,222991326,1075792838,352883826,459345458] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2054510981,1825804774,418288139,378397545,1185114525,81172068,361707637,1111542572] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_70_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_70]
  funext i
  fin_cases i <;> rfl
#print axioms node_70
end R1Z.PV_RunJoin_OutputModel16
