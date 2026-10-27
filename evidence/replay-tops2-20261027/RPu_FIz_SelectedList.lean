import RPu_FIx_SelectedMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_SelectedList
open FIv_NativeValue (K)
theorem value {n : Nat} (a : Fin n → K) (start group lane : Nat) :
    FIx_SelectedMeaning.selected a start group lane=
      if start≤4*group+lane then
        ((List.ofFn a)[4*group+lane-start]?).getD 0 else 0 := by
  unfold FIx_SelectedMeaning.selected
  by_cases lo : start≤4*group+lane
  · rw [if_pos lo]
    by_cases hi : 4*group+lane<start+n
    · rw [dif_pos ⟨lo,hi⟩,List.getElem?_eq_getElem (by simp only [List.length_ofFn];omega),
        Option.getD_some,List.getElem_ofFn]
    · rw [dif_neg (by omega),List.getElem?_eq_none (by simp only [List.length_ofFn];omega)]
      rfl
  · rw [if_neg lo,dif_neg (by omega)]
#print axioms value
end AspisR1.FIz_SelectedList
end
