import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_43_1 : poseidonExternalLinear s_43_0 = s_43_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_1
theorem round_43_2 : poseidonFullRound s_43_1 (poseidonExternalInitial 0) = s_43_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_2
theorem round_43_3 : poseidonFullRound s_43_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_43_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_3
theorem round_43_4 : poseidonFullRound s_43_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_43_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_4
theorem round_43_5 : poseidonFullRound s_43_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_43_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_5
theorem round_43_6 : poseidonInternalRound s_43_5 (poseidonInternalConstants 0) = s_43_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_6
theorem round_43_7 : poseidonInternalRound s_43_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_43_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_7
theorem round_43_8 : poseidonInternalRound s_43_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_43_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_8
theorem round_43_9 : poseidonInternalRound s_43_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_43_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_9
theorem round_43_10 : poseidonInternalRound s_43_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_43_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_10
theorem round_43_11 : poseidonInternalRound s_43_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_43_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_11
theorem round_43_12 : poseidonInternalRound s_43_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_43_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_12
theorem round_43_13 : poseidonInternalRound s_43_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_43_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_13
theorem round_43_14 : poseidonInternalRound s_43_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_43_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_14
theorem round_43_15 : poseidonInternalRound s_43_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_43_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_15
theorem round_43_16 : poseidonInternalRound s_43_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_43_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_16
theorem round_43_17 : poseidonInternalRound s_43_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_43_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_17
theorem round_43_18 : poseidonInternalRound s_43_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_43_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_18
theorem round_43_19 : poseidonInternalRound s_43_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_43_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_19
theorem round_43_20 : poseidonFullRound s_43_19 (poseidonExternalFinal 0) = s_43_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_20
theorem round_43_21 : poseidonFullRound s_43_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_43_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_21
theorem round_43_22 : poseidonFullRound s_43_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_43_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_22
theorem round_43_23 : poseidonFullRound s_43_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_43_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_43_23
theorem permutation_43 : poseidonPermutation s_43_0 = s_43_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_43_1,round_43_2,round_43_3,round_43_4,round_43_5,round_43_6,round_43_7,round_43_8,round_43_9,round_43_10,round_43_11,round_43_12,round_43_13,round_43_14,round_43_15,round_43_16,round_43_17,round_43_18,round_43_19,round_43_20,round_43_21,round_43_22,round_43_23]
#print axioms permutation_43
theorem node_43 : nodeCompress (![1133998657,190536997,632216762,2145002820,1218690534,1341831920,1813986794,962659369] : Fin 8 → Scalar) ![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] = ![1061398933,509112012,1799578086,482877258,2025164722,672733548,359961336,1470147015] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1133998657,190536997,632216762,2145002820,1218690534,1341831920,1813986794,962659369] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_43_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_43]
  funext i
  fin_cases i <;> rfl
#print axioms node_43
end R1Z.PV_RunJoin_OutputModel16
