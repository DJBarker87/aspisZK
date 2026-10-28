import TerminalArrayFromFnModelV4Clean
set_option autoImplicit false
namespace NDH_FromFnTotal
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

theorem loop_total {T F : Type} (N : Usize)
    (cb : core.ops.function.FnMut F Usize T) (state : F) (value : Usize → T)
    (stable : ∀ i : Usize, i.val < N.val → cb.call_mut state i = ok (value i,state))
    (fuel : Nat) (i : Usize) (acc : List T)
    (domain : i.val ≤ N.val) (budget : N.val-i.val < fuel) :
    ∃ out, arrayFromFnLoop N cb fuel i state acc = ok (out,state) := by
  induction fuel generalizing i acc with
  | zero => omega
  | succ fuel ih =>
    by_cases test : i < N
    · have small : i.val < N.val := by simpa only [UScalar.lt_equiv] using test
      have maxN : N.val ≤ Usize.max := by
        have hNsize : N.val < 2 ^ Usize.numBits := by
          simpa only [Usize.numBits, UScalarTy.Usize_numBits_eq] using N.hBounds
        have hmax : Usize.max + 1 = 2 ^ Usize.numBits := by
          rw [Usize.numBits]
          exact Usize.max_succ_eq_pow
        omega
      have hadd : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
        apply UScalar.add_spec
        simpa only [UScalar.max_USize_eq, UScalar.ofNatCore_val_eq] using (show i.val+1≤Usize.max by omega)
      obtain ⟨j,hj,jv⟩ := WP.spec_imp_exists hadd
      obtain ⟨out,run⟩ := ih j (value i::acc) (by omega) (by omega)
      refine ⟨out, ?_⟩
      simp only [arrayFromFnLoop,test,if_pos,stable i small,bind_tc_ok,hj,run]
    · refine ⟨acc.reverse, ?_⟩
      simp only [arrayFromFnLoop,test,if_false]

#print axioms loop_total
end NDH_FromFnTotal
