import NCV_Loop
set_option autoImplicit false
namespace NDB_RejectWitness
open Aeneas Aeneas.Std Result
/-- Local rejection may return a private accumulator; retain it existentially. -/
theorem run {S B : Type}
    (body : (S × Usize) → Result (ControlFlow (S × Usize) B))
    (bad : Nat) (property : B → Prop)
    (steps : ∀ (s : S) (i : Usize), i.val<bad → ∃ next : Usize, ∃ out : S,
      next.val=i.val+1 ∧ body (s,i)=ok (.cont (out,next)))
    (reject : ∀ (s : S) (i : Usize), i.val=bad → ∃ out : B,
      body (s,i)=ok (.done out) ∧ property out)
    (s : S) (i : Usize) (bound : i.val ≤ bad) :
    ∃ out : B, loop body (s,i)=ok out ∧ property out := by
  have all : ∀ k : Nat, ∀ (s : S) (i : Usize), i.val ≤ bad → bad-i.val=k →
      ∃ out : B, loop body (s,i)=ok out ∧ property out := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s i hi hk
      by_cases done : i.val=bad
      · obtain ⟨out,step,post⟩:=reject s i done
        exact ⟨out,NCV_Loop.done _ _ _ step,post⟩
      · obtain ⟨next,acc,value,step⟩:=steps s i (by omega)
        obtain ⟨out,call,post⟩:=ih (bad-next.val) (by omega) acc next (by omega) rfl
        exact ⟨out,(NCV_Loop.cont _ _ _ step).trans call,post⟩
  exact all (bad-i.val) s i bound rfl
#print axioms run
end NDB_RejectWitness
