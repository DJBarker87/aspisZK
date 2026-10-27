import QueryScanConcreteWordsDecoder
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRv_FromFnTotal
open AspisR1SelectedMaskProbe

theorem loop {T F : Type} (N : Usize)
 (callback : core.ops.function.FnMut F Usize T) (value : Nat → T)
 (fuel : Nat) (i : Usize) (f : F) (acc : List T)
 (hi : i.val ≤ N.val) (budget : N.val - i.val ≤ fuel)
 (stable : ∀ j : Usize, j.val < N.val → callback.call_mut f j = ok (value j.val,f)) :
 ∃ out, arrayFromFnLoop N callback fuel i f acc = ok (out,f) := by
 induction fuel generalizing i acc with
 | zero =>
   have hn : ¬ i < N := by simpa only [UScalar.lt_equiv] using (show ¬ i.val < N.val by omega)
   exact ⟨acc.reverse, by simp only [arrayFromFnLoop, hn, ↓reduceDIte]⟩
 | succ fuel ih =>
   by_cases hlt : i < N
   · have hv : i.val < N.val := by simpa only [UScalar.lt_equiv] using hlt
     have hmax : N.val ≤ Usize.max := by scalar_tac
     have hadd : (i + 1#usize : Result Usize) ⦃z => z.val = i.val + 1⦄ := by
       apply UScalar.add_spec
       simp only [UScalar.ofNatCore_val_eq, UScalar.max_USize_eq]
       omega
     obtain ⟨j,hj,hv'⟩ := WP.spec_imp_exists hadd
     obtain ⟨out,hout⟩ := ih j (value i.val :: acc) (by omega) (by omega)
     exact ⟨out, by simp only [arrayFromFnLoop,hlt,↓reduceDIte,stable i hv,bind_tc_ok,hj,hout]⟩
   · exact ⟨acc.reverse, by simp only [arrayFromFnLoop,hlt,↓reduceDIte]⟩

theorem total {T F : Type} (N : Usize)
 (callback : core.ops.function.FnMut F Usize T) (value : Nat → T) (f : F)
 (stable : ∀ j : Usize, j.val < N.val → callback.call_mut f j = ok (value j.val,f)) :
 ∃ out, AspisR1SelectedMaskProbe.core.array.from_fn N callback f = ok out := by
 obtain ⟨out,hout⟩ := loop N callback value (N.val+1) 0#usize f [] (by simp) (by simp) stable
 unfold AspisR1SelectedMaskProbe.core.array.from_fn
 simp only [hout]
 exact ⟨_,rfl⟩

#print axioms loop
#print axioms total
end XRv_FromFnTotal
