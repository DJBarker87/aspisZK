import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_55_1 : poseidonExternalLinear s_55_0 = s_55_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_1
theorem round_55_2 : poseidonFullRound s_55_1 (poseidonExternalInitial 0) = s_55_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_2
theorem round_55_3 : poseidonFullRound s_55_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_55_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_3
theorem round_55_4 : poseidonFullRound s_55_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_55_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_4
theorem round_55_5 : poseidonFullRound s_55_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_55_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_5
theorem round_55_6 : poseidonInternalRound s_55_5 (poseidonInternalConstants 0) = s_55_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_6
theorem round_55_7 : poseidonInternalRound s_55_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_55_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_7
theorem round_55_8 : poseidonInternalRound s_55_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_55_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_8
theorem round_55_9 : poseidonInternalRound s_55_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_55_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_9
theorem round_55_10 : poseidonInternalRound s_55_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_55_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_10
theorem round_55_11 : poseidonInternalRound s_55_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_55_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_11
theorem round_55_12 : poseidonInternalRound s_55_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_55_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_12
theorem round_55_13 : poseidonInternalRound s_55_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_55_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_13
theorem round_55_14 : poseidonInternalRound s_55_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_55_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_14
theorem round_55_15 : poseidonInternalRound s_55_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_55_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_15
theorem round_55_16 : poseidonInternalRound s_55_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_55_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_16
theorem round_55_17 : poseidonInternalRound s_55_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_55_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_17
theorem round_55_18 : poseidonInternalRound s_55_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_55_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_18
theorem round_55_19 : poseidonInternalRound s_55_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_55_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_19
theorem round_55_20 : poseidonFullRound s_55_19 (poseidonExternalFinal 0) = s_55_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_20
theorem round_55_21 : poseidonFullRound s_55_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_55_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_21
theorem round_55_22 : poseidonFullRound s_55_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_55_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_22
theorem round_55_23 : poseidonFullRound s_55_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_55_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_55_23
theorem permutation_55 : poseidonPermutation s_55_0 = s_55_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_55_1,round_55_2,round_55_3,round_55_4,round_55_5,round_55_6,round_55_7,round_55_8,round_55_9,round_55_10,round_55_11,round_55_12,round_55_13,round_55_14,round_55_15,round_55_16,round_55_17,round_55_18,round_55_19,round_55_20,round_55_21,round_55_22,round_55_23]
#print axioms permutation_55
theorem node_55 : nodeCompress (![126701447,2048228689,1569040746,816942090,934340682,707737539,1640113194,1531834504] : Fin 8 → Scalar) ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] = ![2007593611,263026897,269045574,218491882,465723479,2019127874,1644297524,121114825] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![126701447,2048228689,1569040746,816942090,934340682,707737539,1640113194,1531834504] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_55_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_55]
  funext i
  fin_cases i <;> rfl
#print axioms node_55
end R1Z.PV_RunJoin_OutputModel16
