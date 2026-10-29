import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_29_1 : poseidonExternalLinear s_29_0 = s_29_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_1
theorem round_29_2 : poseidonFullRound s_29_1 (poseidonExternalInitial 0) = s_29_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_2
theorem round_29_3 : poseidonFullRound s_29_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_29_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_3
theorem round_29_4 : poseidonFullRound s_29_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_29_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_4
theorem round_29_5 : poseidonFullRound s_29_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_29_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_5
theorem round_29_6 : poseidonInternalRound s_29_5 (poseidonInternalConstants 0) = s_29_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_6
theorem round_29_7 : poseidonInternalRound s_29_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_29_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_7
theorem round_29_8 : poseidonInternalRound s_29_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_29_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_8
theorem round_29_9 : poseidonInternalRound s_29_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_29_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_9
theorem round_29_10 : poseidonInternalRound s_29_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_29_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_10
theorem round_29_11 : poseidonInternalRound s_29_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_29_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_11
theorem round_29_12 : poseidonInternalRound s_29_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_29_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_12
theorem round_29_13 : poseidonInternalRound s_29_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_29_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_13
theorem round_29_14 : poseidonInternalRound s_29_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_29_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_14
theorem round_29_15 : poseidonInternalRound s_29_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_29_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_15
theorem round_29_16 : poseidonInternalRound s_29_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_29_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_16
theorem round_29_17 : poseidonInternalRound s_29_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_29_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_17
theorem round_29_18 : poseidonInternalRound s_29_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_29_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_18
theorem round_29_19 : poseidonInternalRound s_29_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_29_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_19
theorem round_29_20 : poseidonFullRound s_29_19 (poseidonExternalFinal 0) = s_29_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_20
theorem round_29_21 : poseidonFullRound s_29_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_29_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_21
theorem round_29_22 : poseidonFullRound s_29_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_29_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_22
theorem round_29_23 : poseidonFullRound s_29_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_29_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_29_23
theorem permutation_29 : poseidonPermutation s_29_0 = s_29_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_29_1,round_29_2,round_29_3,round_29_4,round_29_5,round_29_6,round_29_7,round_29_8,round_29_9,round_29_10,round_29_11,round_29_12,round_29_13,round_29_14,round_29_15,round_29_16,round_29_17,round_29_18,round_29_19,round_29_20,round_29_21,round_29_22,round_29_23]
theorem node_29 : nodeCompress (![3201,3218,3235,3252,3269,3286,3303,3320] : Fin 8 → Scalar) ![407525056,1458948676,1930040251,1044760048,961029422,441494278,1982425121,1368876468] = ![71235157,561336479,2021715933,831357912,593948515,110335229,1732475008,949858646] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![3201,3218,3235,3252,3269,3286,3303,3320] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![407525056,1458948676,1930040251,1044760048,961029422,441494278,1982425121,1368876468] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![407525056,1458948676,1930040251,1044760048,961029422,441494278,1982425121,1368876468] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_29_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_29]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_29
#print axioms node_29
end R1Z.PV_RunJoin_PathModel16
