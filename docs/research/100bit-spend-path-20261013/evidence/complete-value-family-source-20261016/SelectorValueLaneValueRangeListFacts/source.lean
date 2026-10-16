import R0P.Value

/-! Pointwise lookup facts for the retained 33-cell value-range list. These
are the list-side counterpart to the generated source array contracts and do
not unfold reconstruction recurrences. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneValueRangeListFacts

variable {K : Type} [Field K]

theorem first_block (o : R0P.Openings K) (i : Fin 10) :
    (R0P.valueRange o)[i.val]'(by simp [R0P.valueRange]; omega) =
      (o.z (i.castAdd 6))^2 - o.z (i.castAdd 6) := by
  have h20 : i.val < 10 + 10 := by omega
  have h30 : i.val < 10 + 10 + 10 := by omega
  simp only [R0P.valueRange, List.getElem_append, List.length_append,
    List.length_ofFn, List.getElem_ofFn, dif_pos h30, dif_pos h20,
    dif_pos i.isLt]

theorem second_block (o : R0P.Openings K) (i : Fin 10) :
    (R0P.valueRange o)[10 + i.val]'(by simp [R0P.valueRange]; omega) =
      (o.succ (i.castAdd 6))^2 - o.succ (i.castAdd 6) := by
  have h20 : 10 + i.val < 10 + 10 := by omega
  have h30 : 10 + i.val < 10 + 10 + 10 := by omega
  have hn10 : ¬ 10 + i.val < 10 := by omega
  simp only [R0P.valueRange, List.getElem_append, List.length_append,
    List.length_ofFn, List.getElem_ofFn, dif_pos h30, dif_pos h20,
    dif_neg hn10]
  have hsub : 10 + i.val - 10 = i.val := by omega
  have hindex : (⟨10 + i.val - 10, by omega⟩ : Fin 10) = i := Fin.ext hsub
  rw [hindex]

theorem third_block (o : R0P.Openings K) (i : Fin 10) :
    (R0P.valueRange o)[20 + i.val]'(by simp [R0P.valueRange]; omega) =
      (o.xor12 (i.castAdd 6))^2 - o.xor12 (i.castAdd 6) := by
  have h30 : 20 + i.val < 10 + 10 + 10 := by omega
  have hn20 : ¬ 20 + i.val < 10 + 10 := by omega
  have hn10 : ¬ 20 + i.val < 10 := by omega
  simp only [R0P.valueRange, List.getElem_append, List.length_append,
    List.length_ofFn, List.getElem_ofFn, dif_pos h30, dif_neg hn20,
    dif_neg hn10]
  have hsub : 20 + i.val - (10 + 10) = i.val := by omega
  have hindex : (⟨20 + i.val - (10 + 10), by omega⟩ : Fin 10) = i := Fin.ext hsub
  rw [hindex]

theorem reconstruction_tail (o : R0P.Openings K) :
    (R0P.valueRange o)[30]'(by simp [R0P.valueRange]) =
      o.z 10 - ((R0P.valueReconstruct10 o.z +
        R0P.valueReconstruct10 o.succ * (1024 : K)) +
        R0P.valueReconstruct10 o.xor12 * (1048576 : K)) := by
  simp [R0P.valueRange]

theorem succ_tail (o : R0P.Openings K) :
    (R0P.valueRange o)[31]'(by simp [R0P.valueRange]) = o.succ 10 := by
  simp [R0P.valueRange]

theorem xor_tail (o : R0P.Openings K) :
    (R0P.valueRange o)[32]'(by simp [R0P.valueRange]) = o.xor12 10 := by
  simp [R0P.valueRange]

#print axioms first_block
#print axioms second_block
#print axioms third_block
#print axioms reconstruction_tail
#print axioms succ_tail
#print axioms xor_tail
end AspisR1.SelectorValueLaneValueRangeListFacts
