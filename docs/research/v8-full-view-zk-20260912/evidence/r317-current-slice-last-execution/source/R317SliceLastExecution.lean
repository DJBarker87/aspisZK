import AspisR316SliceLastRaw

/-! Universal result of the emitted actual `Slice.last` body. The subtraction
and read succeed from the valid Slice length bound and the original guard;
there is no supplied success premise or nonempty assumption. -/
set_option autoImplicit false
namespace AspisV8R19.R317SliceLastExecution
open Aeneas Aeneas.Std Result WP

theorem last_complete {T : Type} (xs : Slice T) :
    AspisR316SliceLastRaw.core.slice.Slice.last xs = .ok xs.val.getLast? := by
  by_cases h : 1 ≤ xs.length
  · have hge : Slice.len xs ≥ 1#usize := by
      simpa only [UScalar.le_equiv, Slice.len_val,
        show (1#usize).val = 1 from by simp] using h
    obtain ⟨i, hi, hiv, _⟩ := spec_imp_exists (Usize.sub_spec
      (x := Slice.len xs) (y := 1#usize)
      (by simpa only [Slice.len_val,
        show (1#usize).val = 1 from by simp] using h))
    change UScalar.sub (Slice.len xs) 1#usize = .ok i at hi
    change 1 ≤ xs.val.length at h
    have hv : i.val = xs.val.length - 1 := by
      simpa only [Slice.len_val, Slice.length,
        show (1#usize).val = 1 from by simp] using hiv
    have hb : i.val < xs.val.length := by omega
    simp only [AspisR316SliceLastRaw.core.slice.Slice.last, hge, ↓reduceIte,
      hi, bind_tc_ok, Slice.index_usize, Slice.getElem?_Usize_eq,
      List.getElem?_eq_getElem hb, bind_tc_ok, List.getLast?_eq_getElem?]
    simp only [← hv, List.getElem?_eq_getElem hb]
  · have hz : xs.val.length = 0 := by
      change ¬ 1 ≤ xs.val.length at h
      omega
    have he : xs.val = [] := List.length_eq_zero_iff.mp hz
    have hge : ¬ Slice.len xs ≥ 1#usize := by
      simpa only [UScalar.le_equiv, Slice.len_val,
        show (1#usize).val = 1 from by simp] using h
    simp only [AspisR316SliceLastRaw.core.slice.Slice.last, hge, ↓reduceIte,
      he, List.getLast?_nil]

theorem last_none_iff {T : Type} (xs : Slice T) :
    AspisR316SliceLastRaw.core.slice.Slice.last xs = .ok none ↔ xs.val = [] := by
  rw [last_complete]
  simp

#print axioms last_complete
#print axioms last_none_iff
end AspisV8R19.R317SliceLastExecution
