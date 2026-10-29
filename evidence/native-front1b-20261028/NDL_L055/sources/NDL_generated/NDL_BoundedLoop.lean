import Aeneas
set_option autoImplicit false
namespace NDL_BoundedLoop
open Aeneas Aeneas.Std Result ControlFlow
abbrev Iter := core.ops.range.Range Usize

/-- Generic finite forward-loop induction. State stays abstract, so no
reducibility change to an imported closure carrier is needed. -/
theorem total {C R : Type} (limit : Nat)
    (step : Iter × C → Result (ControlFlow (Iter × C) R))
    (inv : Iter → C → Prop) (post : R → Prop)
    (active : ∀ it c,it.end.val=limit → it.start.val < it.end.val → inv it c →
      ∃ rest next,step (it,c)=ok (cont (rest,next)) ∧
        rest.start.val=it.start.val+1 ∧ rest.end.val=limit ∧ inv rest next)
    (stopped : ∀ it c,it.end.val ≤ it.start.val → inv it c →
      ∃ out,step (it,c)=ok (done out) ∧ post out)
    (iter : Iter) (state : C) (last : iter.end.val=limit)
    (cap : iter.start.val≤limit) (initial : inv iter state) :
    ∃ out,loop step (iter,state)=ok out ∧ post out := by
  let invariant : Iter × C → Prop := fun s =>
    s.1.end.val=limit ∧ s.1.start.val≤limit ∧ inv s.1 s.2
  have spec : WP.spec (loop step (iter,state)) post := by
    apply loop.spec_decr_nat (fun s : Iter × C=>limit-s.1.start.val) invariant post step (iter,state)
    · rintro ⟨it,c⟩ ⟨finish,bound,valid⟩
      change it.end.val=limit at finish
      change it.start.val≤limit at bound
      change inv it c at valid
      by_cases more : it.start.val < it.end.val
      · obtain ⟨rest,next,run,inc,ending,after⟩ := active it c finish more valid
        rw [run,WP.spec_ok]
        change (rest.end.val=limit ∧ rest.start.val≤limit ∧ inv rest next) ∧
          limit-rest.start.val < limit-it.start.val
        exact ⟨⟨ending,by omega,after⟩,by omega⟩
      · obtain ⟨out,run,good⟩ := stopped it c (by omega) valid
        rw [run,WP.spec_ok]
        exact good
    · exact ⟨last,cap,initial⟩
  exact WP.spec_imp_exists spec

#print axioms total
end NDL_BoundedLoop
