import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_69_1 : poseidonExternalLinear s_69_0 = s_69_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_1
theorem round_69_2 : poseidonFullRound s_69_1 (poseidonExternalInitial 0) = s_69_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_2
theorem round_69_3 : poseidonFullRound s_69_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_69_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_3
theorem round_69_4 : poseidonFullRound s_69_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_69_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_4
theorem round_69_5 : poseidonFullRound s_69_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_69_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_5
theorem round_69_6 : poseidonInternalRound s_69_5 (poseidonInternalConstants 0) = s_69_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_6
theorem round_69_7 : poseidonInternalRound s_69_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_69_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_7
theorem round_69_8 : poseidonInternalRound s_69_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_69_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_8
theorem round_69_9 : poseidonInternalRound s_69_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_69_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_9
theorem round_69_10 : poseidonInternalRound s_69_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_69_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_10
theorem round_69_11 : poseidonInternalRound s_69_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_69_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_11
theorem round_69_12 : poseidonInternalRound s_69_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_69_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_12
theorem round_69_13 : poseidonInternalRound s_69_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_69_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_13
theorem round_69_14 : poseidonInternalRound s_69_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_69_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_14
theorem round_69_15 : poseidonInternalRound s_69_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_69_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_15
theorem round_69_16 : poseidonInternalRound s_69_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_69_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_16
theorem round_69_17 : poseidonInternalRound s_69_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_69_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_17
theorem round_69_18 : poseidonInternalRound s_69_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_69_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_18
theorem round_69_19 : poseidonInternalRound s_69_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_69_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_19
theorem round_69_20 : poseidonFullRound s_69_19 (poseidonExternalFinal 0) = s_69_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_20
theorem round_69_21 : poseidonFullRound s_69_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_69_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_21
theorem round_69_22 : poseidonFullRound s_69_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_69_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_22
theorem round_69_23 : poseidonFullRound s_69_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_69_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_69_23
theorem permutation_69 : poseidonPermutation s_69_0 = s_69_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_69_1,round_69_2,round_69_3,round_69_4,round_69_5,round_69_6,round_69_7,round_69_8,round_69_9,round_69_10,round_69_11,round_69_12,round_69_13,round_69_14,round_69_15,round_69_16,round_69_17,round_69_18,round_69_19,round_69_20,round_69_21,round_69_22,round_69_23]
#print axioms permutation_69
theorem node_69 : nodeCompress (![844628622,2057670925,2054832692,931597647,1691905484,10140345,2116907504,1823343454] : Fin 8 → Scalar) ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] = ![2054510981,1825804774,418288139,378397545,1185114525,81172068,361707637,1111542572] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![844628622,2057670925,2054832692,931597647,1691905484,10140345,2116907504,1823343454] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_69_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_69]
  funext i
  fin_cases i <;> rfl
#print axioms node_69
end R1Z.PV_RunJoin_OutputModel16
