import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_75_1 : poseidonExternalLinear s_75_0 = s_75_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_1
theorem round_75_2 : poseidonFullRound s_75_1 (poseidonExternalInitial 0) = s_75_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_2
theorem round_75_3 : poseidonFullRound s_75_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_75_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_3
theorem round_75_4 : poseidonFullRound s_75_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_75_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_4
theorem round_75_5 : poseidonFullRound s_75_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_75_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_5
theorem round_75_6 : poseidonInternalRound s_75_5 (poseidonInternalConstants 0) = s_75_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_6
theorem round_75_7 : poseidonInternalRound s_75_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_75_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_7
theorem round_75_8 : poseidonInternalRound s_75_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_75_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_8
theorem round_75_9 : poseidonInternalRound s_75_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_75_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_9
theorem round_75_10 : poseidonInternalRound s_75_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_75_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_10
theorem round_75_11 : poseidonInternalRound s_75_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_75_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_11
theorem round_75_12 : poseidonInternalRound s_75_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_75_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_12
theorem round_75_13 : poseidonInternalRound s_75_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_75_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_13
theorem round_75_14 : poseidonInternalRound s_75_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_75_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_14
theorem round_75_15 : poseidonInternalRound s_75_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_75_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_15
theorem round_75_16 : poseidonInternalRound s_75_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_75_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_16
theorem round_75_17 : poseidonInternalRound s_75_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_75_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_17
theorem round_75_18 : poseidonInternalRound s_75_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_75_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_18
theorem round_75_19 : poseidonInternalRound s_75_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_75_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_19
theorem round_75_20 : poseidonFullRound s_75_19 (poseidonExternalFinal 0) = s_75_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_20
theorem round_75_21 : poseidonFullRound s_75_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_75_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_21
theorem round_75_22 : poseidonFullRound s_75_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_75_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_22
theorem round_75_23 : poseidonFullRound s_75_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_75_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_75_23
theorem permutation_75 : poseidonPermutation s_75_0 = s_75_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_75_1,round_75_2,round_75_3,round_75_4,round_75_5,round_75_6,round_75_7,round_75_8,round_75_9,round_75_10,round_75_11,round_75_12,round_75_13,round_75_14,round_75_15,round_75_16,round_75_17,round_75_18,round_75_19,round_75_20,round_75_21,round_75_22,round_75_23]
#print axioms permutation_75
theorem node_75 : nodeCompress (![1669216135,741703000,562283949,1060793623,1378667390,256051405,1303928677,1488857718] : Fin 8 → Scalar) ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] = ![1385985564,1312452205,34748210,2022077470,1837706654,827038403,1892640303,370983584] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1669216135,741703000,562283949,1060793623,1378667390,256051405,1303928677,1488857718] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_75_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_75]
  funext i
  fin_cases i <;> rfl
#print axioms node_75
end R1Z.PV_RunJoin_OutputModel16
