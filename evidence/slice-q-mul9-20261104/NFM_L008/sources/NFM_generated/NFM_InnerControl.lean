import NFM_Control
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AspisR1.NFM_InnerControl
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize

def enumerate : Nat → Nat → List Nat
  | 0,_ => []
  | fuel+1,start => start::enumerate fuel (start+1)

def projected : Nat → Range → Result (List Nat)
  | 0,_ => ok []
  | fuel+1,iter => do
    let (item,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
    match item with
    | none => ok []
    | some term => do
      let rest ← projected fuel next
      ok (term.val::rest)

theorem active (iter : Range) (inside : iter.start.val < iter.end.val) :
    ∃ next,core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=
      ok (some iter.start,next) ∧ next.start.val=iter.start.val+1 ∧ next.end=iter.end := by
  obtain ⟨⟨item,next⟩,run,value,start,finish⟩:=WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter inside)
  subst item
  exact ⟨next,run,start,finish⟩

theorem complete (fuel : Nat) (iter : Range)
    (span : iter.start.val+fuel=iter.end.val) :
    projected fuel iter=ok (enumerate fuel iter.start.val) := by
  induction fuel generalizing iter with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨next,run,advance,finish⟩:=active iter (by omega)
    have remaining : next.start.val+fuel=next.end.val := by rw [advance,finish];omega
    simp only [projected,run,bind_tc_ok,Aeneas.Std.uncurry,ih next remaining,advance,enumerate]

/-- Exact actual Range.next control inside every emitted outer cut. -/
theorem at_cut (k : Fin 7) :
    projected
      ((NFA_Iterator.cursor ⟨k.val+1,by omega⟩).val-
       (NFA_Iterator.cursor ⟨k.val,by omega⟩).val)
      {start:=NFA_Iterator.cursor ⟨k.val,by omega⟩,
       «end»:=NFA_Iterator.cursor ⟨k.val+1,by omega⟩}=
      ok ((NFM_Control.terms (4*k.val)).map Prod.snd) := by
  rw [complete _ _ (by fin_cases k <;> decide)]
  fin_cases k <;> rfl

#print axioms active
#print axioms complete
#print axioms at_cut
end AspisR1.NFM_InnerControl
