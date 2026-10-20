import QueryScanConcreteWordsDecoder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1SelectedMaskProbe

theorem arrayFromFnLoop_total_of_stable {T F : Type} {N : Usize}
    (callback : core.ops.function.FnMut F Usize T) (value : Nat → T)
    (fuel : Nat) (i : Usize) (f : F) (acc : List T)
    (hi : i.val ≤ N.val) (hbudget : N.val-i.val ≤ fuel)
    (hstable : ∀ j : Usize, j.val < N.val → callback.call_mut f j = .ok (value j.val,f)) :
    ∃ out, arrayFromFnLoop N callback fuel i f acc = .ok (out,f) := by
  induction fuel generalizing i acc with
  | zero =>
      have hn : ¬ i < N := by
        intro h
        have hv : i.val < N.val := by simpa only [UScalar.lt_equiv] using h
        omega
      exact ⟨acc.reverse,by simp only [arrayFromFnLoop,hn,dif_neg]⟩
  | succ fuel ih =>
      by_cases hlt : i < N
      · have hiv : i.val < N.val := by simpa only [UScalar.lt_equiv] using hlt
        have hNmax : N.val ≤ Usize.max := by
          have hbound : N.val < 2^Usize.numBits := by
            simpa [Usize.numBits,UScalarTy.Usize_numBits_eq] using N.hBounds
          have hmax : Usize.max+1=2^Usize.numBits := by
            rw [Usize.numBits];exact Usize.max_succ_eq_pow
          omega
        have haddSpec : (i+1#usize : Result Usize) ⦃j => j.val=i.val+1⦄ := by
          apply UScalar.add_spec
          have hone : (1#usize).val=1 := by scalar_tac
          simpa only [hone,UScalar.max_USize_eq] using (show i.val+1 ≤ Usize.max by omega)
        obtain ⟨j,hadd,hj⟩ := WP.spec_imp_exists haddSpec
        obtain ⟨out,hout⟩ := ih j (value i.val::acc) (by omega) (by omega)
        exact ⟨out,by simp only [arrayFromFnLoop,hlt,dif_pos,hstable i hiv,bind_tc_ok,hadd,hout]⟩
      · exact ⟨acc.reverse,by simp only [arrayFromFnLoop,hlt,dif_neg]⟩

theorem arrayFromFn_stable_total {T F : Type} {N : Usize}
    (callback : core.ops.function.FnMut F Usize T) (value : Nat → T) (f : F)
    (hstable : ∀ j : Usize, j.val < N.val → callback.call_mut f j = .ok (value j.val,f)) :
    ∃ out : Array T N,
      core.array.from_fn N callback f = .ok out ∧ out.val=(List.range N.val).map value := by
  obtain ⟨values,hloop⟩ := arrayFromFnLoop_total_of_stable callback value (N.val+1)
    0#usize f [] (by simp) (by omega) hstable
  have hlen := arrayFromFnLoop_length_of_success N callback (N.val+1) 0#usize f []
    values f (by simp) (by simp) (by omega) hloop
  have hvals := arrayFromFnLoop_values_of_stable callback value (N.val+1) 0#usize f []
    values f (by simp) (by omega) (by simp) hstable hloop
  refine ⟨⟨values,hlen⟩,?_,hvals.1⟩
  unfold core.array.from_fn
  split
  · rename_i values1 fout heq
    have hp : (values1,fout)=(values,f) := Result.ok.inj (heq.symm.trans hloop)
    cases hp
    rfl
  · rename_i error heq
    have hb : Result.fail error = Result.ok (values,f) := heq.symm.trans hloop
    cases hb
  · rename_i heq
    have hb : Result.div = Result.ok (values,f) := heq.symm.trans hloop
    cases hb

#print axioms arrayFromFnLoop_total_of_stable
#print axioms arrayFromFn_stable_total
end AspisR1SelectedMaskProbe
