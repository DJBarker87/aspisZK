import R1Z.PV_RJDec_Factor
set_option autoImplicit false
namespace R1Z.PV_RJDec_ResultCases
open PV_W_Threading PV_RunJoin_WorldDecode33 PV_RJDec_Factor
variable {W C A V : Type}

/-- Success retains the value and final world, but no outcome retains calls
in the old carrier. Failure/divergence retain neither world nor calls. -/
theorem returned_eq (l r : Run W C Aeneas.Std.Error A) :
    returned l = returned r ↔
      (∃ a, l.outcome=.ok a ∧ r.outcome=.ok a ∧ l.world=r.world) ∨
      (∃ e, l.outcome=.fail e ∧ r.outcome=.fail e) ∨
      (l.outcome=.div ∧ r.outcome=.div) := by
  cases l with | mk lo lw lc =>
    cases r with | mk ro rw rc =>
      cases lo <;> cases ro <;> simp [returned,eq_comm]

/-- An exhaustive obligation, including outer fail/div and every inner
Result rejection carried as an ordinary successful value of A. -/
theorem fibres_iff
    (reachable : Run W C Aeneas.Std.Error A → Prop)
    (observe : Run W C Aeneas.Std.Error A → V) :
    Fibres reachable observe ↔
      (∀ l r a, reachable l → reachable r → l.outcome=.ok a →
        r.outcome=.ok a → l.world=r.world → observe l=observe r) ∧
      (∀ l r e, reachable l → reachable r → l.outcome=.fail e →
        r.outcome=.fail e → observe l=observe r) ∧
      (∀ l r, reachable l → reachable r → l.outcome=.div →
        r.outcome=.div → observe l=observe r) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro l r a hl hr hol hor hw
      exact h l r hl hr ((returned_eq l r).mpr (.inl ⟨a,hol,hor,hw⟩))
    · intro l r e hl hr hol hor
      exact h l r hl hr ((returned_eq l r).mpr (.inr (.inl ⟨e,hol,hor⟩)))
    · intro l r hl hr hol hor
      exact h l r hl hr ((returned_eq l r).mpr (.inr (.inr ⟨hol,hor⟩)))
  · rintro ⟨hs,hf,hd⟩ l r hl hr same
    rcases (returned_eq l r).mp same with ⟨a,hol,hor,hw⟩ | ⟨e,hol,hor⟩ | ⟨hol,hor⟩
    · exact hs l r a hl hr hol hor hw
    · exact hf l r e hl hr hol hor
    · exact hd l r hl hr hol hor
#print axioms returned_eq
#print axioms fibres_iff
end R1Z.PV_RJDec_ResultCases
