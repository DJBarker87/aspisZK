import SCH_TableAfter
set_option autoImplicit false
namespace AspisR1.SCH_CollisionAppend
open FS AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I]

theorem append (bad : I → Table I A → A → Prop) (t : Table I A)
    (prior suffix : List (I × A)) :
    hitsBad bad t (prior ++ suffix) ↔
      hitsBad bad t prior ∨ hitsBad bad (SCH_TableAfter.after t prior) suffix := by
  induction prior generalizing t with
  | nil => simp only [List.nil_append,hitsBad,SCH_TableAfter.after,false_or]
  | cons q rest ih =>
    simpa only [List.cons_append,hitsBad,SCH_TableAfter.after,ih,or_assoc]

/-- A suffix of cached addresses cannot create another first-read event. -/
theorem cached (bad : I → Table I A → A → Prop) (t : Table I A)
    (suffix : List (I × A)) (known : ∀ q ∈ suffix, t q.1 ≠ none) :
    ¬ hitsBad bad t suffix := by
  induction suffix generalizing t with
  | nil => simp only [hitsBad,not_false_eq_true]
  | cons q rest ih =>
    have present := known q (List.mem_cons_self)
    have tail : ∀ r ∈ rest, put t q.1 q.2 r.1 ≠ none := by
      intro r member
      exact SCH_TableAfter.put_keeps _ _ _ _ (known r (List.mem_cons_of_mem _ member))
    simp only [hitsBad,present,false_and,false_or]
    exact ih (put t q.1 q.2) tail

#print axioms append
#print axioms cached
end AspisR1.SCH_CollisionAppend
