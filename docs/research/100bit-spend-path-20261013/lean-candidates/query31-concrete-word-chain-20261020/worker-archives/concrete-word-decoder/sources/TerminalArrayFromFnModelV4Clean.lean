import TerminalStandardOperationModelsV1

/-!
Generic executable model for Rust `array::from_fn` at the Aeneas operation
boundary. The model traverses indices in order, calls the `FnMut` exactly once
at each visited index, threads its returned state, and accumulates values
without requiring `Copy` or a dummy initializer. Its Rust-library
correspondence is a separate obligation; this file only establishes the
operational model and its successful output length.
-/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe

def arrayFromFnLoop {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) :
    Nat → Usize → F → List T → Result (List T × F)
  | fuel, i, f, acc =>
      if h : i < N then
        match fuel with
        | 0 => .div
        | fuel + 1 => do
            let (value, f') ← callback.call_mut f i
            let i' ← i + 1#usize
            arrayFromFnLoop N callback fuel i' f' (value :: acc)
      else
        .ok (acc.reverse, f)
termination_by fuel _ _ _ => fuel
decreasing_by all_goals simp_wf

theorem arrayFromFnLoop_length_of_success
    {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T)
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (out : List T) (fout : F)
    (hi : i.val ≤ N.val) (hacc : acc.length = i.val)
    (hbudget : N.val - i.val ≤ fuel)
    (hrun : arrayFromFnLoop N callback fuel i f acc = .ok (out, fout)) :
    out.length = N.val := by
  induction fuel generalizing i f acc out fout with
  | zero =>
      have hnot : ¬ i < N := by
        intro hlt
        have hltv : i.val < N.val := by
          simpa only [UScalar.lt_equiv] using hlt
        omega
      simp only [arrayFromFnLoop, hnot] at hrun
      cases Result.ok.inj hrun
      simp [hacc]
      omega
  | succ fuel ih =>
      by_cases hlt : i < N
      · have hltv : i.val < N.val := by
          simpa only [UScalar.lt_equiv] using hlt
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
        cases hcall : callback.call_mut f i with
        | fail e => simp [hcall] at hrun
        | div => simp [hcall] at hrun
        | ok pair =>
            rcases pair with ⟨value, f'⟩
            simp only [hcall, bind_tc_ok] at hrun
            cases hnext : (i + 1#usize : Result Usize) with
            | fail e => simp [hnext] at hrun
            | div => simp [hnext] at hrun
            | ok i'' =>
                have hi'' : i'' = i' := Result.ok.inj (hnext.symm.trans hadd)
                subst i''
                simp only [hnext, bind_tc_ok] at hrun
                have hi'val : i'.val = i.val + 1 := hi'
                have hi'le : i'.val ≤ N.val := by rw [hi'val]; omega
                have hacc' : (value :: acc).length = i'.val := by
                  simp [hacc, hi'val]
                have hbudget' : N.val - i'.val ≤ fuel := by
                  rw [hi'val]
                  omega
                exact ih i' f' (value :: acc) out fout hi'le hacc' hbudget' hrun
      · have hival : i.val = N.val := by
          have hnotval : ¬ i.val < N.val := by
            intro h
            apply hlt
            simpa only [UScalar.lt_equiv] using h
          omega
        simp only [arrayFromFnLoop, hlt] at hrun
        cases Result.ok.inj hrun
        simp [hacc, hival]

def core.array.from_fn
    {T F : Type} (N : Usize)
    (callback : core.ops.function.FnMut F Usize T) (f : F) :
    Result (Array T N) :=
  match h : arrayFromFnLoop N callback (N.val + 1) 0#usize f [] with
  | .ok (values, _) =>
      .ok ⟨values, arrayFromFnLoop_length_of_success N callback (N.val + 1)
        0#usize f [] values _ (by simp) (by simp) (by omega) h⟩
  | .fail error => .fail error
  | .div => .div

#print axioms arrayFromFnLoop
#print axioms arrayFromFnLoop_length_of_success
#print axioms core.array.from_fn

end AspisR1SelectedMaskProbe
