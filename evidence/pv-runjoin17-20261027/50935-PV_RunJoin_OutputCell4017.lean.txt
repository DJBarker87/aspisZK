import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_40_1 : poseidonExternalLinear s_40_0 = s_40_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_1
theorem round_40_2 : poseidonFullRound s_40_1 (poseidonExternalInitial 0) = s_40_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_2
theorem round_40_3 : poseidonFullRound s_40_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_40_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_3
theorem round_40_4 : poseidonFullRound s_40_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_40_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_4
theorem round_40_5 : poseidonFullRound s_40_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_40_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_5
theorem round_40_6 : poseidonInternalRound s_40_5 (poseidonInternalConstants 0) = s_40_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_6
theorem round_40_7 : poseidonInternalRound s_40_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_40_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_7
theorem round_40_8 : poseidonInternalRound s_40_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_40_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_8
theorem round_40_9 : poseidonInternalRound s_40_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_40_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_9
theorem round_40_10 : poseidonInternalRound s_40_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_40_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_10
theorem round_40_11 : poseidonInternalRound s_40_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_40_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_11
theorem round_40_12 : poseidonInternalRound s_40_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_40_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_12
theorem round_40_13 : poseidonInternalRound s_40_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_40_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_13
theorem round_40_14 : poseidonInternalRound s_40_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_40_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_14
theorem round_40_15 : poseidonInternalRound s_40_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_40_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_15
theorem round_40_16 : poseidonInternalRound s_40_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_40_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_16
theorem round_40_17 : poseidonInternalRound s_40_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_40_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_17
theorem round_40_18 : poseidonInternalRound s_40_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_40_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_18
theorem round_40_19 : poseidonInternalRound s_40_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_40_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_19
theorem round_40_20 : poseidonFullRound s_40_19 (poseidonExternalFinal 0) = s_40_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_20
theorem round_40_21 : poseidonFullRound s_40_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_40_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_21
theorem round_40_22 : poseidonFullRound s_40_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_40_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_22
theorem round_40_23 : poseidonFullRound s_40_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_40_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_40_23
theorem permutation_40 : poseidonPermutation s_40_0 = s_40_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_40_1,round_40_2,round_40_3,round_40_4,round_40_5,round_40_6,round_40_7,round_40_8,round_40_9,round_40_10,round_40_11,round_40_12,round_40_13,round_40_14,round_40_15,round_40_16,round_40_17,round_40_18,round_40_19,round_40_20,round_40_21,round_40_22,round_40_23]
#print axioms permutation_40
theorem node_40 : nodeCompress (![263935107,2015801952,2126421827,1338328324,66681051,462846977,1805190326,1770497381] : Fin 8 → Scalar) ![0,0,0,0,0,0,0,0] = ![1635444076,565453809,2007649881,905247732,1187015924,827186728,137720039,588419202] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![263935107,2015801952,2126421827,1338328324,66681051,462846977,1805190326,1770497381] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_40_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_40]
  funext i
  fin_cases i <;> rfl
#print axioms node_40
end R1Z.PV_RunJoin_OutputModel16
