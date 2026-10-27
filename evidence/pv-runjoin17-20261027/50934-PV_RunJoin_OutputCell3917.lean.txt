import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_39_1 : poseidonExternalLinear s_39_0 = s_39_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_1
theorem round_39_2 : poseidonFullRound s_39_1 (poseidonExternalInitial 0) = s_39_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_2
theorem round_39_3 : poseidonFullRound s_39_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_39_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_3
theorem round_39_4 : poseidonFullRound s_39_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_39_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_4
theorem round_39_5 : poseidonFullRound s_39_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_39_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_5
theorem round_39_6 : poseidonInternalRound s_39_5 (poseidonInternalConstants 0) = s_39_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_6
theorem round_39_7 : poseidonInternalRound s_39_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_39_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_7
theorem round_39_8 : poseidonInternalRound s_39_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_39_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_8
theorem round_39_9 : poseidonInternalRound s_39_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_39_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_9
theorem round_39_10 : poseidonInternalRound s_39_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_39_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_10
theorem round_39_11 : poseidonInternalRound s_39_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_39_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_11
theorem round_39_12 : poseidonInternalRound s_39_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_39_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_12
theorem round_39_13 : poseidonInternalRound s_39_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_39_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_13
theorem round_39_14 : poseidonInternalRound s_39_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_39_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_14
theorem round_39_15 : poseidonInternalRound s_39_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_39_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_15
theorem round_39_16 : poseidonInternalRound s_39_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_39_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_16
theorem round_39_17 : poseidonInternalRound s_39_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_39_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_17
theorem round_39_18 : poseidonInternalRound s_39_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_39_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_18
theorem round_39_19 : poseidonInternalRound s_39_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_39_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_19
theorem round_39_20 : poseidonFullRound s_39_19 (poseidonExternalFinal 0) = s_39_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_20
theorem round_39_21 : poseidonFullRound s_39_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_39_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_21
theorem round_39_22 : poseidonFullRound s_39_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_39_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_22
theorem round_39_23 : poseidonFullRound s_39_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_39_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_39_23
theorem permutation_39 : poseidonPermutation s_39_0 = s_39_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_39_1,round_39_2,round_39_3,round_39_4,round_39_5,round_39_6,round_39_7,round_39_8,round_39_9,round_39_10,round_39_11,round_39_12,round_39_13,round_39_14,round_39_15,round_39_16,round_39_17,round_39_18,round_39_19,round_39_20,round_39_21,round_39_22,round_39_23]
#print axioms permutation_39
theorem node_39 : nodeCompress (![1443258150,390107157,739124880,1925983251,420127778,800761649,949547039,74873928] : Fin 8 → Scalar) ![109581603,2018382657,1175266929,551563770,389056008,563172097,1431420963,351017421] = ![1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,2134856457] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1443258150,390107157,739124880,1925983251,420127778,800761649,949547039,74873928] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![109581603,2018382657,1175266929,551563770,389056008,563172097,1431420963,351017421] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![109581603,2018382657,1175266929,551563770,389056008,563172097,1431420963,351017421] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_39_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_39]
  funext i
  fin_cases i <;> rfl
#print axioms node_39
end R1Z.PV_RunJoin_OutputModel16
