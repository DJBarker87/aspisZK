import NCV_Loop
set_option autoImplicit false
namespace NDB_ScanDecision
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def Suffix (good : Nat → Prop) (n start : Nat) : Prop := ∀ j, start ≤ j → j<n → good j

theorem run (body : Usize → Result (ControlFlow Usize (Option Bool)))
    (good : Nat → Prop) (n : Nat)
    (steps : ∀ i : Usize, i.val<n → ∃ next : Usize, next.val=i.val+1 ∧
      body i=ok (if good i.val then .cont next else .done (some false)))
    (terminal : ∀ i : Usize, n ≤ i.val → body i=ok (.done none))
    (i : Usize) (bound : i.val ≤ n) :
    loop body i=ok (if Suffix good n i.val then none else some false) := by
  classical
  have all : ∀ k : Nat, ∀ i : Usize, i.val ≤ n → n-i.val=k →
      loop body i=ok (if Suffix good n i.val then none else some false) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi hk
      by_cases done : n ≤ i.val
      · have goodAll : Suffix good n i.val := by intro j hj hn;omega
        rw [NCV_Loop.done _ _ _ (terminal i done),if_pos goodAll]
      · obtain ⟨next,value,step⟩:=steps i (by omega)
        by_cases test : good i.val
        · rw [if_pos test] at step
          have suffix : Suffix good n i.val ↔ Suffix good n next.val := by
            constructor
            · intro h j hj hn;exact h j (by omega) hn
            · intro h j hj hn
              by_cases same : j=i.val
              · simpa only [same] using test
              · exact h j (by omega) hn
          rw [NCV_Loop.cont _ _ _ step,ih (n-next.val) (by omega) next (by omega) rfl,
            propext suffix]
        · rw [if_neg test] at step
          have bad : ¬Suffix good n i.val := by intro h;exact test (h i.val (by omega) (by omega))
          rw [NCV_Loop.done _ _ _ step,if_neg bad]
  exact all (n-i.val) i bound rfl
#print axioms run
end NDB_ScanDecision
