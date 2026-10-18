import SequentialFreshProgram

namespace AspisR1.SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.SequentialFreshProgram

/-- A property of every terminating answer branch, without assuming a law
for the answers or a consistent oracle at the original addresses. -/
def AllOutcomes {I A O : Type} : Program I A O → (O → Prop) → Prop
  | .done o, P => P o
  | .ask _ next, P => ∀ a, AllOutcomes (next a) P

theorem all_mono {I A O : Type} (p : Program I A O) {P Q : O → Prop}
    (hp : AllOutcomes p P) (h : ∀ o, P o → Q o) : AllOutcomes p Q := by
  induction p with
  | done o => exact h o hp
  | ask i next ih => exact fun a => ih a (hp a)

theorem all_bind {I A O U : Type} (p : Program I A O)
    (next : O → Program I A U) (P : U → Prop)
    (hp : AllOutcomes p (fun o => AllOutcomes (next o) P)) :
    AllOutcomes (bind p next) P := by
  induction p with
  | done o => exact hp
  | ask i k ih => exact fun a => ih a (hp a)

theorem all_eval {I A O : Type} (H : I → A) (p : Program I A O)
    (P : O → Prop) (hp : AllOutcomes p P) : P (eval H p).2 := by
  induction p with
  | done o => exact hp
  | ask i next ih => exact ih (H i) (hp (H i))

theorem sequential_bind {I A O U : Type} (p : Program I A O)
    (next : O → Program I A U) (cursor : Nat) :
    sequential (bind p next) cursor =
      bind (sequential p cursor) (fun oc => sequential (next oc.1) oc.2) := by
  induction p generalizing cursor with
  | done o => rfl
  | ask i k ih =>
    change Program.ask cursor (fun a => sequential (bind (k a) next) (cursor+1)) =
      Program.ask cursor (fun a =>
        bind (sequential (k a) (cursor+1)) (fun oc => sequential (next oc.1) oc.2))
    congr 1
    funext a
    exact ih a (cursor+1)

theorem all_sequential {I A O : Type} (p : Program I A O) (P : O → Prop)
    (hp : AllOutcomes p P) (cursor : Nat) :
    AllOutcomes (sequential p cursor) (fun oc => P oc.1) := by
  induction p generalizing cursor with
  | done o => exact hp
  | ask i next ih => exact fun a => ih a (hp a) (cursor+1)

/-- The cursor is exactly the initial cursor plus the actual interpreter's
query-trace length; it is not merely an assigned budget counter. -/
theorem sequential_eval_cursor {I A O : Type} (H : Nat → A)
    (p : Program I A O) (cursor : Nat) :
    (eval H (sequential p cursor)).2.2 =
      cursor + (eval H (sequential p cursor)).1.length := by
  induction p generalizing cursor with
  | done o => simp only [sequential, eval, List.length_nil, Nat.add_zero]
  | ask i next ih =>
    simp only [sequential, eval, List.length_cons]
    have h := ih (H cursor) (cursor+1)
    omega

#print axioms AllOutcomes
#print axioms all_mono
#print axioms all_bind
#print axioms all_eval
#print axioms sequential_bind
#print axioms all_sequential
#print axioms sequential_eval_cursor
end AspisR1.SequentialProgramInvariants
