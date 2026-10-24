import TerminalArrayFromFnModelV4Clean
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
theorem finish_arrayFromFnLoop_exec_of_stable
    {T F : Type} {N : Usize}
    (callback : core.ops.function.FnMut F Usize T) (value : Nat → T)
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (hi : i.val ≤ N.val) (hbudget : N.val - i.val ≤ fuel)
    (hacc : acc.reverse = (List.range i.val).map value)
    (hstable : ∀ j : Usize, j.val < N.val →
      callback.call_mut f j = .ok (value j.val, f)) :
    arrayFromFnLoop N callback fuel i f acc =
      .ok ((List.range N.val).map value, f) := by
  induction fuel generalizing i f acc with
  | zero =>
      have hnot : ¬ i < N := by
        intro hlt
        have hltv : i.val < N.val := by
          simpa only [UScalar.lt_equiv] using hlt
        omega
      have hiN : i.val = N.val := by omega
      simp [arrayFromFnLoop, hnot, hacc, hiN]
  | succ fuel ih =>
      by_cases hlt : i < N
      · have hltv : i.val < N.val := by
          simpa only [UScalar.lt_equiv] using hlt
        have hcall := hstable i hltv
        have hNbound : N.val ≤ Usize.max := by
          have hNsize : N.val < 2 ^ Usize.numBits := by
            simpa [Usize.numBits, UScalarTy.Usize_numBits_eq] using N.hBounds
          have hmax : Usize.max + 1 = 2 ^ Usize.numBits := by
            rw [Usize.numBits]
            exact Usize.max_succ_eq_pow
          omega
        have haddBound : i.val + 1 ≤ Usize.max := by omega
        have haddSpec : (i + 1#usize : Result Usize) ⦃ j => j.val = i.val + 1 ⦄ := by
          apply UScalar.add_spec
          have hone : (1#usize).val = 1 := by scalar_tac
          simpa only [hone, UScalar.max_USize_eq] using haddBound
        obtain ⟨i', hadd, hi'⟩ := Aeneas.Std.WP.spec_imp_exists haddSpec
        have hi'val : i'.val = i.val + 1 := hi'
        have hi'le : i'.val ≤ N.val := by rw [hi'val]; omega
        have hbudget' : N.val - i'.val ≤ fuel := by rw [hi'val]; omega
        have hacc' : (value i.val :: acc).reverse =
            (List.range i'.val).map value := by
          rw [List.reverse_cons, hacc, hi'val, List.range_succ]
          simp
        have hrec := ih i' f (value i.val :: acc) hi'le hbudget' hacc' hstable
        simp [arrayFromFnLoop, hlt, hcall, hadd, hrec]
      · have hiN : i.val = N.val := by
          have hnotval : ¬ i.val < N.val := by
            intro h
            apply hlt
            simpa only [UScalar.lt_equiv] using h
          omega
        simp [arrayFromFnLoop, hlt, hacc, hiN]


#print axioms finish_arrayFromFnLoop_exec_of_stable
end AspisR1SelectedMaskProbe
