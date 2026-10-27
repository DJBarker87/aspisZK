import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_67_1 : poseidonExternalLinear s_67_0 = s_67_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_1
theorem round_67_2 : poseidonFullRound s_67_1 (poseidonExternalInitial 0) = s_67_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_2
theorem round_67_3 : poseidonFullRound s_67_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_67_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_3
theorem round_67_4 : poseidonFullRound s_67_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_67_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_4
theorem round_67_5 : poseidonFullRound s_67_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_67_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_5
theorem round_67_6 : poseidonInternalRound s_67_5 (poseidonInternalConstants 0) = s_67_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_6
theorem round_67_7 : poseidonInternalRound s_67_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_67_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_7
theorem round_67_8 : poseidonInternalRound s_67_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_67_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_8
theorem round_67_9 : poseidonInternalRound s_67_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_67_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_9
theorem round_67_10 : poseidonInternalRound s_67_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_67_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_10
theorem round_67_11 : poseidonInternalRound s_67_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_67_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_11
theorem round_67_12 : poseidonInternalRound s_67_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_67_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_12
theorem round_67_13 : poseidonInternalRound s_67_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_67_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_13
theorem round_67_14 : poseidonInternalRound s_67_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_67_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_14
theorem round_67_15 : poseidonInternalRound s_67_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_67_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_15
theorem round_67_16 : poseidonInternalRound s_67_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_67_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_16
theorem round_67_17 : poseidonInternalRound s_67_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_67_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_17
theorem round_67_18 : poseidonInternalRound s_67_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_67_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_18
theorem round_67_19 : poseidonInternalRound s_67_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_67_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_19
theorem round_67_20 : poseidonFullRound s_67_19 (poseidonExternalFinal 0) = s_67_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_20
theorem round_67_21 : poseidonFullRound s_67_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_67_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_21
theorem round_67_22 : poseidonFullRound s_67_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_67_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_22
theorem round_67_23 : poseidonFullRound s_67_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_67_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_67_23
theorem permutation_67 : poseidonPermutation s_67_0 = s_67_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_67_1,round_67_2,round_67_3,round_67_4,round_67_5,round_67_6,round_67_7,round_67_8,round_67_9,round_67_10,round_67_11,round_67_12,round_67_13,round_67_14,round_67_15,round_67_16,round_67_17,round_67_18,round_67_19,round_67_20,round_67_21,round_67_22,round_67_23]
#print axioms permutation_67
theorem node_67 : nodeCompress (![641432107,640429421,874903178,930860174,778988106,1148923135,1488375597,266199979] : Fin 8 → Scalar) ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] = ![719727911,1261141874,1037425088,1528290707,696744339,983928879,1739454800,712455604] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![641432107,640429421,874903178,930860174,778988106,1148923135,1488375597,266199979] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_67_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_67]
  funext i
  fin_cases i <;> rfl
#print axioms node_67
end R1Z.PV_RunJoin_OutputModel16
