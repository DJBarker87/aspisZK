import R1Z.PV_RunJoin_PathData16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathModel16
open R0P
theorem round_19_1 : poseidonExternalLinear s_19_0 = s_19_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_1
theorem round_19_2 : poseidonFullRound s_19_1 (poseidonExternalInitial 0) = s_19_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_2
theorem round_19_3 : poseidonFullRound s_19_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_19_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_3
theorem round_19_4 : poseidonFullRound s_19_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_19_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_4
theorem round_19_5 : poseidonFullRound s_19_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_19_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_5
theorem round_19_6 : poseidonInternalRound s_19_5 (poseidonInternalConstants 0) = s_19_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_6
theorem round_19_7 : poseidonInternalRound s_19_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_19_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_7
theorem round_19_8 : poseidonInternalRound s_19_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_19_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_8
theorem round_19_9 : poseidonInternalRound s_19_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_19_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_9
theorem round_19_10 : poseidonInternalRound s_19_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_19_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_10
theorem round_19_11 : poseidonInternalRound s_19_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_19_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_11
theorem round_19_12 : poseidonInternalRound s_19_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_19_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_12
theorem round_19_13 : poseidonInternalRound s_19_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_19_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_13
theorem round_19_14 : poseidonInternalRound s_19_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_19_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_14
theorem round_19_15 : poseidonInternalRound s_19_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_19_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_15
theorem round_19_16 : poseidonInternalRound s_19_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_19_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_16
theorem round_19_17 : poseidonInternalRound s_19_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_19_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_17
theorem round_19_18 : poseidonInternalRound s_19_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_19_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_18
theorem round_19_19 : poseidonInternalRound s_19_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_19_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_19
theorem round_19_20 : poseidonFullRound s_19_19 (poseidonExternalFinal 0) = s_19_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_20
theorem round_19_21 : poseidonFullRound s_19_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_19_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_21
theorem round_19_22 : poseidonFullRound s_19_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_19_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_22
theorem round_19_23 : poseidonFullRound s_19_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_19_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_23
theorem permutation_19 : poseidonPermutation s_19_0 = s_19_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_19_1,round_19_2,round_19_3,round_19_4,round_19_5,round_19_6,round_19_7,round_19_8,round_19_9,round_19_10,round_19_11,round_19_12,round_19_13,round_19_14,round_19_15,round_19_16,round_19_17,round_19_18,round_19_19,round_19_20,round_19_21,round_19_22,round_19_23]
theorem node_19 : nodeCompress (![784754526,653487580,1331396859,1248357024,70404971,1215624494,880337038,1016952666] : Fin 8 → Scalar) ![2241,2258,2275,2292,2309,2326,2343,2360] = ![1675309617,1189999060,110604265,1111112896,1601727123,1630516452,660958964,1526316434] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![784754526,653487580,1331396859,1248357024,70404971,1215624494,880337038,1016952666] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2241,2258,2275,2292,2309,2326,2343,2360] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2241,2258,2275,2292,2309,2326,2343,2360] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_19_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_19]
  funext i
  fin_cases i <;> rfl
#print axioms permutation_19
#print axioms node_19
end R1Z.PV_RunJoin_PathModel16
