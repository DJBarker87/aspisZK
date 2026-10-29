import NDL_BoundedLoop
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

theorem total (p : Array NE 4#usize) (f : Array NQ 4#usize)
    (hp : ∀ x∈p.val,canonE x) (iter : Iter) (finish : iter.end.val=4)
    (cap : iter.start.val≤4) (v : NE) (hv : canonE v) :
    ∃ out,run iter (p,f) v=ok out ∧ canonE out := by
  let step : Iter × C × NE → Result (ControlFlow (Iter × C × NE) NE) :=
    fun s=>body s.1 s.2.1 s.2.2
  let inv : Iter → C × NE → Prop := fun _ s =>
    (∀ x∈s.1.1.val,canonE x) ∧ canonE s.2
  have active : ∀ it c,it.end.val=4 → it.start.val < it.end.val → inv it c →
      ∃ rest next,step (it,c)=ok (cont (rest,next)) ∧
        rest.start.val=it.start.val+1 ∧ rest.end.val=4 ∧ inv rest next := by
    rintro it ⟨⟨powers,factors⟩,a⟩ last more ⟨cp,ca⟩
    obtain ⟨rest,out,run,inc,last',co⟩ := NCJ_ScalarFoldStep.active powers factors cp a ca it last more
    exact ⟨rest,((powers,factors),out),run,inc,last',cp,co⟩
  have stopped : ∀ it c,it.end.val ≤ it.start.val → inv it c →
      ∃ out,step (it,c)=ok (done out) ∧ canonE out := by
    rintro it ⟨c,a⟩ stop ⟨_,ca⟩
    exact ⟨a,NCJ_ScalarFoldStep.done it a c stop,ca⟩
  exact NDL_BoundedLoop.total 4 step inv canonE active stopped iter ((p,f),v)
    finish cap ⟨hp,hv⟩

#print axioms total
end NDL_ScalarFold
end
