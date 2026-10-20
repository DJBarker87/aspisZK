import TerminalArrayFromFnModelV4
import ArrayFromFnCopyStable

/-! Under a callback that returns the same state at every index, the
state-threaded list-accumulator `from_fn` model and the accepted extracted
`array_from_fn_copy` implementation construct extensionally equal arrays.
The premise is a callback theorem, not an assertion about Rust's standard
library implementation. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

theorem arrayFromFnLoop_values_of_stable
    {T F : Type} {N : Usize}
    (callback : core.ops.function.FnMut F Usize T) (value : Nat → T)
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (out : List T) (fout : F)
    (hi : i.val ≤ N.val) (hbudget : N.val - i.val ≤ fuel)
    (hacc : acc.reverse = (List.range i.val).map value)
    (hstable : ∀ j : Usize, j.val < N.val →
      callback.call_mut f j = .ok (value j.val, f))
    (hrun : arrayFromFnLoop N callback fuel i f acc = .ok (out, fout)) :
    out = (List.range N.val).map value ∧ fout = f := by
  induction fuel generalizing i f acc out fout with
  | zero =>
      have hnot : ¬ i < N := by
        intro hlt
        have hltv : i.val < N.val := by
          simpa only [UScalar.lt_equiv] using hlt
        omega
      simp only [arrayFromFnLoop, hnot] at hrun
      cases Result.ok.inj hrun
      have hiN : i.val = N.val := by omega
      constructor
      · simpa [hiN] using hacc
      · rfl
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
        simp only [arrayFromFnLoop, hlt] at hrun
        rw [hcall, bind_tc_ok] at hrun
        simp only [hadd, bind_tc_ok] at hrun
        have hi'val : i'.val = i.val + 1 := hi'
        have hi'le : i'.val ≤ N.val := by rw [hi'val]; omega
        have hbudget' : N.val - i'.val ≤ fuel := by
          rw [hi'val]
          omega
        have hacc' : (value i.val :: acc).reverse =
            (List.range i'.val).map value := by
          rw [List.reverse_cons, hacc, hi'val, List.range_succ]
          simp
        exact ih i' f (value i.val :: acc) out fout hi'le hbudget' hacc' hstable hrun
      · have hiN : i.val = N.val := by
          have hnotval : ¬ i.val < N.val := by
            intro h
            apply hlt
            simpa only [UScalar.lt_equiv] using h
          omega
        simp only [arrayFromFnLoop, hlt] at hrun
        cases Result.ok.inj hrun
        constructor
        · simpa [hiN] using hacc
        · rfl

theorem arrayFromFnLoop_exec_of_stable
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

theorem core_array_from_fn_eq_copy_of_stable
    {T F : Type} (N : Usize)
    (copyInst : core.marker.Copy T)
    (callback : core.ops.function.FnMut F Usize T)
    (init : T) (f : F) (value : Nat → T)
    (hstable : ∀ i : Usize, i.val < N.val →
      callback.call_mut f i = .ok (value i.val, f)) :
    ∃ out : Array T N,
      AspisR1SelectedMaskProbe.core.array.from_fn N callback f = .ok out ∧
      array_from_fn_copy N copyInst callback init f = .ok out ∧
      ∀ i : Nat, ∀ hi : i < N.val,
        out.val[i]'(by simpa [out.property] using hi) = value i := by
  obtain ⟨copyOut, hcopy, hcopyValue⟩ :=
    array_from_fn_copy_stable N copyInst callback init f value hstable
  have hzero : (0#usize : Usize).val = 0 := by scalar_tac
  have hacc : ([] : List T).reverse = (List.range (0#usize : Usize).val).map value := by
    simp [hzero]
  have hLoop := arrayFromFnLoop_exec_of_stable callback value
    (N.val + 1) 0#usize f [] (by rw [hzero]; omega) (by rw [hzero]; omega)
    hacc hstable
  -- The successful length theorem supplies the dependent array length.  The
  -- output list has the same length because it is indexed by `List.range`.
  have hlen : ((List.range N.val).map value).length = N.val := by simp
  let modelOut : Array T N := ⟨(List.range N.val).map value, hlen⟩
  have hmodel : AspisR1SelectedMaskProbe.core.array.from_fn N callback f = .ok modelOut := by
    unfold AspisR1SelectedMaskProbe.core.array.from_fn
    cases hLoop.symm
    rfl
  have hvals : modelOut.val = copyOut.val := by
    apply List.ext_getElem
    · simp [modelOut, copyOut.property]
    · intro i hi1 hi2
      have hm : modelOut.val[i]'hi1 = value i := by
        simp [modelOut, List.getElem_map, List.getElem_range]
      have hc : copyOut.val[i]'hi2 = value i := hcopyValue i (by simpa [copyOut.property] using hi2)
      rw [hm, hc]
  have heq : modelOut = copyOut := by
    apply Subtype.ext
    exact hvals
  subst copyOut
  refine ⟨modelOut, hmodel, hcopy, ?_⟩
  intro i hi
  have h := hcopyValue i hi
  simpa [modelOut] using h

#print axioms arrayFromFnLoop_values_of_stable
#print axioms core_array_from_fn_eq_copy_of_stable

end AspisR1SelectedMaskProbe
