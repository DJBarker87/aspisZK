import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_74_1 : poseidonExternalLinear s_74_0 = s_74_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_1
theorem round_74_2 : poseidonFullRound s_74_1 (poseidonExternalInitial 0) = s_74_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_2
theorem round_74_3 : poseidonFullRound s_74_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_74_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_3
theorem round_74_4 : poseidonFullRound s_74_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_74_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_4
theorem round_74_5 : poseidonFullRound s_74_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_74_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_5
theorem round_74_6 : poseidonInternalRound s_74_5 (poseidonInternalConstants 0) = s_74_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_6
theorem round_74_7 : poseidonInternalRound s_74_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_74_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_7
theorem round_74_8 : poseidonInternalRound s_74_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_74_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_8
theorem round_74_9 : poseidonInternalRound s_74_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_74_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_9
theorem round_74_10 : poseidonInternalRound s_74_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_74_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_10
theorem round_74_11 : poseidonInternalRound s_74_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_74_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_11
theorem round_74_12 : poseidonInternalRound s_74_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_74_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_12
theorem round_74_13 : poseidonInternalRound s_74_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_74_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_13
theorem round_74_14 : poseidonInternalRound s_74_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_74_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_14
theorem round_74_15 : poseidonInternalRound s_74_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_74_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_15
theorem round_74_16 : poseidonInternalRound s_74_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_74_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_16
theorem round_74_17 : poseidonInternalRound s_74_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_74_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_17
theorem round_74_18 : poseidonInternalRound s_74_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_74_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_18
theorem round_74_19 : poseidonInternalRound s_74_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_74_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_19
theorem round_74_20 : poseidonFullRound s_74_19 (poseidonExternalFinal 0) = s_74_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_20
theorem round_74_21 : poseidonFullRound s_74_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_74_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_21
theorem round_74_22 : poseidonFullRound s_74_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_74_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_22
theorem round_74_23 : poseidonFullRound s_74_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_74_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_74_23
theorem permutation_74 : poseidonPermutation s_74_0 = s_74_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_74_1,round_74_2,round_74_3,round_74_4,round_74_5,round_74_6,round_74_7,round_74_8,round_74_9,round_74_10,round_74_11,round_74_12,round_74_13,round_74_14,round_74_15,round_74_16,round_74_17,round_74_18,round_74_19,round_74_20,round_74_21,round_74_22,round_74_23]
#print axioms permutation_74
theorem node_74 : nodeCompress (![1024910236,34897137,119525087,2069845639,34881120,1632903117,1891593814,1830035060] : Fin 8 → Scalar) ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] = ![1669216135,741703000,562283949,1060793623,1378667390,256051405,1303928677,1488857718] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1024910236,34897137,119525087,2069845639,34881120,1632903117,1891593814,1830035060] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_74_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_74]
  funext i
  fin_cases i <;> rfl
#print axioms node_74
end R1Z.PV_RunJoin_OutputModel16
