import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_20_1 : poseidonExternalLinear s_20_0 = s_20_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_1
theorem round_20_2 : poseidonFullRound s_20_1 (poseidonExternalInitial 0) = s_20_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_2
theorem round_20_3 : poseidonFullRound s_20_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_20_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_3
theorem round_20_4 : poseidonFullRound s_20_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_20_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_4
theorem round_20_5 : poseidonFullRound s_20_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_20_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_5
theorem round_20_6 : poseidonInternalRound s_20_5 (poseidonInternalConstants 0) = s_20_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_6
theorem round_20_7 : poseidonInternalRound s_20_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_20_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_7
theorem round_20_8 : poseidonInternalRound s_20_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_20_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_8
theorem round_20_9 : poseidonInternalRound s_20_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_20_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_9
theorem round_20_10 : poseidonInternalRound s_20_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_20_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_10
theorem round_20_11 : poseidonInternalRound s_20_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_20_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_11
theorem round_20_12 : poseidonInternalRound s_20_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_20_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_12
theorem round_20_13 : poseidonInternalRound s_20_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_20_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_13
theorem round_20_14 : poseidonInternalRound s_20_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_20_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_14
theorem round_20_15 : poseidonInternalRound s_20_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_20_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_15
theorem round_20_16 : poseidonInternalRound s_20_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_20_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_16
theorem round_20_17 : poseidonInternalRound s_20_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_20_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_17
theorem round_20_18 : poseidonInternalRound s_20_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_20_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_18
theorem round_20_19 : poseidonInternalRound s_20_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_20_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_19
theorem round_20_20 : poseidonFullRound s_20_19 (poseidonExternalFinal 0) = s_20_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_20
theorem round_20_21 : poseidonFullRound s_20_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_20_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_21
theorem round_20_22 : poseidonFullRound s_20_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_20_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_22
theorem round_20_23 : poseidonFullRound s_20_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_20_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_23
theorem permutation_20 : poseidonPermutation s_20_0 = s_20_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_20_1,round_20_2,round_20_3,round_20_4,round_20_5,round_20_6,round_20_7,round_20_8,round_20_9,round_20_10,round_20_11,round_20_12,round_20_13,round_20_14,round_20_15,round_20_16,round_20_17,round_20_18,round_20_19,round_20_20,round_20_21,round_20_22,round_20_23]
theorem node_20 : nodeCompress (![1675309617,1189999060,110604265,1111112896,1601727123,1630516452,660958964,1526316434] : Fin 8 → Scalar) ![2261,2278,2295,2312,2329,2346,2363,2380] = ![493855764,1737005017,1044011334,780794261,292608247,1805935865,972083531,346637554] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1675309617,1189999060,110604265,1111112896,1601727123,1630516452,660958964,1526316434] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2261,2278,2295,2312,2329,2346,2363,2380] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2261,2278,2295,2312,2329,2346,2363,2380] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_20_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_20]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_20
#print axioms node_20
end R1Z.PV_RunJoin_PathModel16
