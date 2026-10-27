import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_Loop

theorem next {S R : Type} (f : S → Result (ControlFlow S R)) (s t : S) (v : R)
    (h : f s = ok (.cont t)) (rest : loop f t = ok v) : loop f s = ok v := by
  rw [loop.eq_def,h]
  exact rest
#print axioms next

theorem done {S R : Type} (f : S → Result (ControlFlow S R)) (s : S) (v : R)
    (h : f s = ok (.done v)) : loop f s = ok v := by
  rw [loop.eq_def,h]
#print axioms done

theorem range (i j e : Usize) (lt : i.val < e.val) (inc : j.val = i.val + 1) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize {start:=i,«end»:=e} =
      ok (some i,{start:=j,«end»:=e}) := by
  obtain ⟨v,hv,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_Usize_some_spec {start:=i,«end»:=e} lt)
  rcases v with ⟨o,r⟩
  rcases he with ⟨ho,hr,hend⟩
  have hs : r.start = j := UScalar.eq_imp r.start j (by change r.start.val = i.val+1 at hr; omega)
  have rr : r = {start:=j,«end»:=e} := by cases r; simp_all
  simpa only [ho,rr] using hv
#print axioms range
end SDY_Loop
