import NCJ_ScalarFoldStep
import NDL_ArithmeticCalls
set_option autoImplicit false
noncomputable section
namespace NDL_ScalarFold
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Iter := NCJ_ForwardRange.Range
abbrev C := NCJ_ScalarFoldStep.Closure
abbrev body := NCJ_ScalarFoldStep.body
abbrev run := FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop
  NCJ_ScalarFoldStep.iterator NCJ_ScalarFoldStep.fnmut

/-- Induction over the REAL emitted fold, with immutable closure and canonical
accumulator preserved from one arbitrary pre-state through termination. -/
theorem total (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (hp : ∀ x∈p.val,canonE x) (iter : Iter) (finish : iter.end.val=4)
    (cap : iter.start.val≤4) (v : NE) (hv : canonE v) :
    ∃ out,run iter (p,f) v=ok out ∧ canonE out := by
  let inv : (Iter × C × NE) → Prop := fun s =>
    s.1.end.val=4 ∧ s.1.start.val≤4 ∧ s.2.1=(p,f) ∧ canonE s.2.2
  have spec : WP.spec (run iter (p,f) v) canonE := by
    unfold run FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop
    apply loop.spec_decr_nat (fun s : Iter × C × NE => 4-s.1.start.val) inv canonE
      (fun s=>body s.1 s.2.1 s.2.2) (iter,(p,f),v)
    · rintro ⟨it,c,a⟩ ⟨last,bound,same,ca⟩
      change it.end.val=4 at last
      change it.start.val≤4 at bound
      change c=(p,f) at same
      change canonE a at ca
      subst c
      by_cases more : it.start.val<it.end.val
      · obtain ⟨rest,out,step,inc,last',co⟩ := NCJ_ScalarFoldStep.active p f hp a ca it last more
        rw [step,WP.spec_ok]
        change (rest.end.val=4 ∧ rest.start.val≤4 ∧ (p,f)=(p,f) ∧ canonE out) ∧
          4-rest.start.val<4-it.start.val
        exact ⟨⟨last',by omega,rfl,co⟩,by omega⟩
      · have step := NCJ_ScalarFoldStep.done it a (p,f) (by omega)
        rw [step,WP.spec_ok]
        exact ca
    · exact ⟨finish,cap,rfl,hv⟩
  exact WP.spec_imp_exists spec

#print axioms total
end NDL_ScalarFold
end
