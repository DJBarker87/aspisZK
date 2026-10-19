import OccupancyRangeTraversal

/-! A resource-independent relation for the actual Aeneas partial loop.
Body equality is needed only at reachable invariant states. Successful
continuations must decrease a natural measure. Failure/divergence is preserved
without assuming that either kernel succeeds. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsLoopRelation
open Aeneas Aeneas.Std Result ControlFlow

def All {A : Type} (r : Result A) (P : A → Prop) : Prop :=
  ∀ value, r = .ok value → P value

theorem all_bind {A B : Type} (r : Result A) (k : A → Result B) (P : B → Prop)
    (hk : ∀ value, All (k value) P) : All (r >>= k) P := by
  cases r with
  | fail e => intro value h;cases h
  | div => intro value h;cases h
  | ok value => exact hk value

theorem all_ok {A : Type} (value : A) (P : A → Prop) (h : P value) :
    All (.ok value) P := by
  intro out ho;cases ho;exact h

theorem loop_eq {A B : Type} (newBody oldBody : A → Result (ControlFlow A B))
    (I : A → Prop) (measure : A → Nat)
    (hbody : ∀ state, I state → newBody state = oldBody state)
    (hnext : ∀ state next, I state → oldBody state = .ok (.cont next) →
      I next ∧ measure next < measure state)
    (state : A) (hI : I state) : loop newBody state = loop oldBody state := by
  have aux : ∀ fuel state, measure state = fuel → I state →
      loop newBody state = loop oldBody state := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro state hmeasure hI
      conv_lhs => rw [loop]
      conv_rhs => rw [loop]
      rw [hbody state hI]
      cases ho : oldBody state with
      | fail e => rfl
      | div => rfl
      | ok flow =>
        cases flow with
        | done value => rfl
        | cont next =>
          obtain ⟨hI1,hlt⟩ := hnext state next hI ho
          exact ih (measure next) (by omega) next rfl hI1
  exact aux (measure state) state rfl hI

#print axioms all_bind
#print axioms all_ok
#print axioms loop_eq
end AspisR1.CuSavingsLoopRelation
