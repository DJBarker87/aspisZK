import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_48_1 : poseidonExternalLinear s_48_0 = s_48_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_1
theorem round_48_2 : poseidonFullRound s_48_1 (poseidonExternalInitial 0) = s_48_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_2
theorem round_48_3 : poseidonFullRound s_48_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_48_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_3
theorem round_48_4 : poseidonFullRound s_48_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_48_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_4
theorem round_48_5 : poseidonFullRound s_48_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_48_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_5
theorem round_48_6 : poseidonInternalRound s_48_5 (poseidonInternalConstants 0) = s_48_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_6
theorem round_48_7 : poseidonInternalRound s_48_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_48_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_7
theorem round_48_8 : poseidonInternalRound s_48_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_48_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_8
theorem round_48_9 : poseidonInternalRound s_48_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_48_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_9
theorem round_48_10 : poseidonInternalRound s_48_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_48_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_10
theorem round_48_11 : poseidonInternalRound s_48_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_48_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_11
theorem round_48_12 : poseidonInternalRound s_48_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_48_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_12
theorem round_48_13 : poseidonInternalRound s_48_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_48_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_13
theorem round_48_14 : poseidonInternalRound s_48_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_48_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_14
theorem round_48_15 : poseidonInternalRound s_48_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_48_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_15
theorem round_48_16 : poseidonInternalRound s_48_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_48_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_16
theorem round_48_17 : poseidonInternalRound s_48_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_48_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_17
theorem round_48_18 : poseidonInternalRound s_48_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_48_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_18
theorem round_48_19 : poseidonInternalRound s_48_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_48_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_19
theorem round_48_20 : poseidonFullRound s_48_19 (poseidonExternalFinal 0) = s_48_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_20
theorem round_48_21 : poseidonFullRound s_48_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_48_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_21
theorem round_48_22 : poseidonFullRound s_48_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_48_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_22
theorem round_48_23 : poseidonFullRound s_48_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_48_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_48_23
theorem permutation_48 : poseidonPermutation s_48_0 = s_48_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_48_1,round_48_2,round_48_3,round_48_4,round_48_5,round_48_6,round_48_7,round_48_8,round_48_9,round_48_10,round_48_11,round_48_12,round_48_13,round_48_14,round_48_15,round_48_16,round_48_17,round_48_18,round_48_19,round_48_20,round_48_21,round_48_22,round_48_23]
#print axioms permutation_48
theorem node_48 : nodeCompress (![779813195,274765226,1694692007,261106508,380728998,546229929,1098356305,1560230773] : Fin 8 → Scalar) ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] = ![985515685,670227816,320139735,164221359,586867065,504851391,659699442,1594817757] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![779813195,274765226,1694692007,261106508,380728998,546229929,1098356305,1560230773] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_48_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_48]
  funext i
  fin_cases i <;> rfl
#print axioms node_48
end R1Z.PV_RunJoin_OutputModel16
