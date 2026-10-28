import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_80_1 : poseidonExternalLinear s_80_0 = s_80_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_1
theorem round_80_2 : poseidonFullRound s_80_1 (poseidonExternalInitial 0) = s_80_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_2
theorem round_80_3 : poseidonFullRound s_80_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_80_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_3
theorem round_80_4 : poseidonFullRound s_80_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_80_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_4
theorem round_80_5 : poseidonFullRound s_80_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_80_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_5
theorem round_80_6 : poseidonInternalRound s_80_5 (poseidonInternalConstants 0) = s_80_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_6
theorem round_80_7 : poseidonInternalRound s_80_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_80_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_7
theorem round_80_8 : poseidonInternalRound s_80_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_80_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_8
theorem round_80_9 : poseidonInternalRound s_80_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_80_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_9
theorem round_80_10 : poseidonInternalRound s_80_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_80_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_10
theorem round_80_11 : poseidonInternalRound s_80_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_80_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_11
theorem round_80_12 : poseidonInternalRound s_80_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_80_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_12
theorem round_80_13 : poseidonInternalRound s_80_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_80_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_13
theorem round_80_14 : poseidonInternalRound s_80_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_80_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_14
theorem round_80_15 : poseidonInternalRound s_80_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_80_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_15
theorem round_80_16 : poseidonInternalRound s_80_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_80_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_16
theorem round_80_17 : poseidonInternalRound s_80_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_80_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_17
theorem round_80_18 : poseidonInternalRound s_80_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_80_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_18
theorem round_80_19 : poseidonInternalRound s_80_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_80_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_19
theorem round_80_20 : poseidonFullRound s_80_19 (poseidonExternalFinal 0) = s_80_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_20
theorem round_80_21 : poseidonFullRound s_80_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_80_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_21
theorem round_80_22 : poseidonFullRound s_80_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_80_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_22
theorem round_80_23 : poseidonFullRound s_80_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_80_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_80_23
theorem permutation_80 : poseidonPermutation s_80_0 = s_80_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_80_1,round_80_2,round_80_3,round_80_4,round_80_5,round_80_6,round_80_7,round_80_8,round_80_9,round_80_10,round_80_11,round_80_12,round_80_13,round_80_14,round_80_15,round_80_16,round_80_17,round_80_18,round_80_19,round_80_20,round_80_21,round_80_22,round_80_23]
#print axioms permutation_80
theorem node_80 : nodeCompress (![1898472488,597255419,137386091,1805069421,1817944500,96708207,529143660,294781830] : Fin 8 → Scalar) ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] = ![1292873940,403060133,431852686,2044395979,1025272584,521204804,1571926865,345135516] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1898472488,597255419,137386091,1805069421,1817944500,96708207,529143660,294781830] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_80_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_80]
  funext i
  fin_cases i <;> rfl
#print axioms node_80
end R1Z.PV_RunJoin_OutputModel16
