import R1Z.PV_RunJoin_OutputData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputModel16
open R0P
theorem round_68_1 : poseidonExternalLinear s_68_0 = s_68_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_1
theorem round_68_2 : poseidonFullRound s_68_1 (poseidonExternalInitial 0) = s_68_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_2
theorem round_68_3 : poseidonFullRound s_68_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_68_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_3
theorem round_68_4 : poseidonFullRound s_68_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_68_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_4
theorem round_68_5 : poseidonFullRound s_68_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_68_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_5
theorem round_68_6 : poseidonInternalRound s_68_5 (poseidonInternalConstants 0) = s_68_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_6
theorem round_68_7 : poseidonInternalRound s_68_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_68_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_7
theorem round_68_8 : poseidonInternalRound s_68_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_68_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_8
theorem round_68_9 : poseidonInternalRound s_68_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_68_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_9
theorem round_68_10 : poseidonInternalRound s_68_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_68_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_10
theorem round_68_11 : poseidonInternalRound s_68_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_68_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_11
theorem round_68_12 : poseidonInternalRound s_68_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_68_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_12
theorem round_68_13 : poseidonInternalRound s_68_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_68_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_13
theorem round_68_14 : poseidonInternalRound s_68_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_68_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_14
theorem round_68_15 : poseidonInternalRound s_68_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_68_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_15
theorem round_68_16 : poseidonInternalRound s_68_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_68_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_16
theorem round_68_17 : poseidonInternalRound s_68_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_68_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_17
theorem round_68_18 : poseidonInternalRound s_68_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_68_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_18
theorem round_68_19 : poseidonInternalRound s_68_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_68_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_19
theorem round_68_20 : poseidonFullRound s_68_19 (poseidonExternalFinal 0) = s_68_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_20
theorem round_68_21 : poseidonFullRound s_68_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_68_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_21
theorem round_68_22 : poseidonFullRound s_68_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_68_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_22
theorem round_68_23 : poseidonFullRound s_68_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_68_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_68_23
theorem permutation_68 : poseidonPermutation s_68_0 = s_68_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_68_1,round_68_2,round_68_3,round_68_4,round_68_5,round_68_6,round_68_7,round_68_8,round_68_9,round_68_10,round_68_11,round_68_12,round_68_13,round_68_14,round_68_15,round_68_16,round_68_17,round_68_18,round_68_19,round_68_20,round_68_21,round_68_22,round_68_23]
#print axioms permutation_68
theorem node_68 : nodeCompress (![719727911,1261141874,1037425088,1528290707,696744339,983928879,1739454800,712455604] : Fin 8 → Scalar) ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] = ![844628622,2057670925,2054832692,931597647,1691905484,10140345,2116907504,1823343454] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![719727911,1261141874,1037425088,1528290707,696744339,983928879,1739454800,712455604] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_68_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_68]
  funext i
  fin_cases i <;> rfl
#print axioms node_68
end R1Z.PV_RunJoin_OutputModel16
