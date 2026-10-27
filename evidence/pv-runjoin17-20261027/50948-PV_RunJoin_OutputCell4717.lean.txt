import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_47_1 : poseidonExternalLinear s_47_0 = s_47_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_1
theorem round_47_2 : poseidonFullRound s_47_1 (poseidonExternalInitial 0) = s_47_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_2
theorem round_47_3 : poseidonFullRound s_47_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_47_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_3
theorem round_47_4 : poseidonFullRound s_47_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_47_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_4
theorem round_47_5 : poseidonFullRound s_47_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_47_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_5
theorem round_47_6 : poseidonInternalRound s_47_5 (poseidonInternalConstants 0) = s_47_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_6
theorem round_47_7 : poseidonInternalRound s_47_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_47_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_7
theorem round_47_8 : poseidonInternalRound s_47_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_47_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_8
theorem round_47_9 : poseidonInternalRound s_47_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_47_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_9
theorem round_47_10 : poseidonInternalRound s_47_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_47_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_10
theorem round_47_11 : poseidonInternalRound s_47_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_47_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_11
theorem round_47_12 : poseidonInternalRound s_47_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_47_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_12
theorem round_47_13 : poseidonInternalRound s_47_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_47_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_13
theorem round_47_14 : poseidonInternalRound s_47_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_47_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_14
theorem round_47_15 : poseidonInternalRound s_47_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_47_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_15
theorem round_47_16 : poseidonInternalRound s_47_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_47_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_16
theorem round_47_17 : poseidonInternalRound s_47_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_47_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_17
theorem round_47_18 : poseidonInternalRound s_47_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_47_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_18
theorem round_47_19 : poseidonInternalRound s_47_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_47_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_19
theorem round_47_20 : poseidonFullRound s_47_19 (poseidonExternalFinal 0) = s_47_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_20
theorem round_47_21 : poseidonFullRound s_47_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_47_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_21
theorem round_47_22 : poseidonFullRound s_47_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_47_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_22
theorem round_47_23 : poseidonFullRound s_47_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_47_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_47_23
theorem permutation_47 : poseidonPermutation s_47_0 = s_47_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_47_1,round_47_2,round_47_3,round_47_4,round_47_5,round_47_6,round_47_7,round_47_8,round_47_9,round_47_10,round_47_11,round_47_12,round_47_13,round_47_14,round_47_15,round_47_16,round_47_17,round_47_18,round_47_19,round_47_20,round_47_21,round_47_22,round_47_23]
#print axioms permutation_47
theorem node_47 : nodeCompress (![874162269,1451641120,2103371390,1001754857,1905791956,1847859879,128353993,1497851806] : Fin 8 → Scalar) ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] = ![779813195,274765226,1694692007,261106508,380728998,546229929,1098356305,1560230773] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![874162269,1451641120,2103371390,1001754857,1905791956,1847859879,128353993,1497851806] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_47_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_47]
  funext i
  fin_cases i <;> rfl
#print axioms node_47
end R1Z.PV_RunJoin_OutputModel16
