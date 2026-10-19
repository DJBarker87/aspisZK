import SequentialProgramInvariants

namespace AspisR1.ProgramQueryCost
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.SequentialProgramInvariants AspisR1.SequentialFreshProgram

/-- Every terminating answer branch, carrying the actual number of asks.
There is no successful-run or probability assumption. -/
def AllCosts {I A O : Type} : Program I A O → (O → Nat → Prop) → Prop
  | .done o, P => P o 0
  | .ask _ next, P => ∀ a, AllCosts (next a) (fun o n => P o (n+1))

variable {I A O U : Type}

theorem allCosts_true (p : Program I A O) : AllCosts p (fun _ _ => True) := by
  induction p with
  | done o => trivial
  | ask i k ih => exact ih

theorem allCosts_mono (p : Program I A O) {P Q : O → Nat → Prop}
    (hp : AllCosts p P) (h : ∀ o n, P o n → Q o n) : AllCosts p Q := by
  induction p generalizing P Q with
  | done o => exact h o 0 hp
  | ask i k ih => exact fun a => ih a (hp a) (fun o n => h o (n+1))

theorem allCosts_and (p : Program I A O) {P Q : O → Nat → Prop}
    (hp : AllCosts p P) (hq : AllCosts p Q) :
    AllCosts p (fun o n => P o n ∧ Q o n) := by
  induction p generalizing P Q with
  | done o => exact ⟨hp,hq⟩
  | ask i k ih => exact fun a => ih a (hp a) (hq a)

theorem allCosts_of_all (p : Program I A O) (P : O → Prop)
    (hp : AllOutcomes p P) : AllCosts p (fun o _ => P o) := by
  induction p with
  | done o => exact hp
  | ask i k ih => exact fun a => ih a (hp a)

theorem allCosts_bind (p : Program I A O) (next : O → Program I A U)
    (P : U → Nat → Prop)
    (hp : AllCosts p (fun o n => AllCosts (next o) (fun u m => P u (n+m)))) :
    AllCosts (bind p next) P := by
  induction p generalizing P with
  | done o =>
    change AllCosts (next o) P
    change AllCosts (next o) (fun u m => P u (0+m)) at hp
    simpa only [Nat.zero_add] using hp
  | ask i k ih =>
    intro a
    apply ih a (fun u n => P u (n+1))
    apply allCosts_mono _ (hp a)
    intro o n ho
    apply allCosts_mono _ ho
    intro u m hu
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu

/-- The outer sequential cursor counts exactly the asks in AllCosts. -/
theorem allCosts_sequential (p : Program I A O) (P : O → Nat → Prop)
    (hp : AllCosts p P) (cursor : Nat) :
    AllOutcomes (sequential p cursor) (fun oc =>
      ∃ n, oc.2 = cursor+n ∧ P oc.1 n) := by
  induction p generalizing P cursor with
  | done o => exact ⟨0,rfl,hp⟩
  | ask i k ih =>
    intro a
    apply all_mono _ (ih a (fun o n => P o (n+1)) (hp a) (cursor+1))
    intro oc ho
    obtain ⟨n,hn,hP⟩ := ho
    exact ⟨n+1,by omega,hP⟩

/-- A program already sequenced internally also reports its actual ask count;
an outer sequencing pass will not create or remove asks. -/
theorem allCosts_sequential_cursor (p : Program I A O) (cursor : Nat) :
    AllCosts (sequential p cursor) (fun oc n => oc.2 = cursor+n) := by
  induction p generalizing cursor with
  | done o => rfl
  | ask i k ih =>
    intro a
    apply allCosts_mono _ (ih a (cursor+1))
    intro oc n hn
    omega

#print axioms AllCosts
#print axioms allCosts_true
#print axioms allCosts_mono
#print axioms allCosts_and
#print axioms allCosts_of_all
#print axioms allCosts_bind
#print axioms allCosts_sequential
#print axioms allCosts_sequential_cursor
end AspisR1.ProgramQueryCost
