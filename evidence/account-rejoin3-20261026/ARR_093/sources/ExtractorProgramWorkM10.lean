import ExtractorWorkMonad
import SequentialProgramInvariants

/-! Writer composition for the actual causal Program datatype. Pure work is
retained independently of oracle asks. Thus scalar preparation and terminal
checks are paid even on paths with no oracle query. -/
set_option autoImplicit false
namespace AspisR1.ExtractorProgramWorkM10
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SequentialFreshProgram SequentialProgramInvariants

abbrev WorkProgram (I A X : Type) := Program I A (X × Nat)

def map {I A X Y : Type} (f : X → Y) : Program I A X → Program I A Y
  | .done x => .done (f x)
  | .ask i next => .ask i (fun a => map f (next a))

def erase {I A X : Type} (p : WorkProgram I A X) : Program I A X := map Prod.fst p

def pure {I A X : Type} (x : X) (n : Nat) : WorkProgram I A X := .done (x,n)

def lift {I A X : Type} (p : Program I A X) (n : Nat) : WorkProgram I A X :=
  map (fun x => (x,n)) p

def bind {I A X Y : Type} (p : WorkProgram I A X)
    (next : X → WorkProgram I A Y) : WorkProgram I A Y :=
  AspisV8R19.OracleProgramOps.bind p (fun x => map (fun y => (y.1,x.2+y.2)) (next x.1))

theorem map_map {I A X Y Z : Type} (f : X → Y) (g : Y → Z) (p : Program I A X) :
    map g (map f p) = map (g ∘ f) p := by
  induction p with
  | done x => rfl
  | ask i next ih =>
    change Program.ask i _ = Program.ask i _
    congr 1
    funext a
    exact ih a

theorem map_id {I A X : Type} (p : Program I A X) : map id p = p := by
  induction p with
  | done x => rfl
  | ask i next ih =>
    change Program.ask i _ = Program.ask i _
    congr 1
    funext a
    exact ih a

theorem erase_lift {I A X : Type} (p : Program I A X) (n : Nat) :
    erase (lift p n) = p := by
  unfold erase lift
  rw [map_map]
  exact map_id p

theorem erase_bind {I A X Y : Type} (p : WorkProgram I A X)
    (next : X → WorkProgram I A Y) :
    erase (bind p next) =
      AspisV8R19.OracleProgramOps.bind (erase p) (fun x => erase (next x)) := by
  induction p with
  | done x =>
    simp only [bind, AspisV8R19.OracleProgramOps.bind, erase, map, map_map]
    rfl
  | ask i k ih =>
    change Program.ask i _ = Program.ask i _
    congr 1
    funext a
    exact ih a

theorem all_map {I A X Y : Type} (p : Program I A X) (f : X → Y)
    (P : Y → Prop) (h : AllOutcomes p (fun x => P (f x))) :
    AllOutcomes (map f p) P := by
  induction p with
  | done x => exact h
  | ask i next ih => exact fun a => ih a (h a)

theorem lift_bound {I A X : Type} (p : Program I A X) (n : Nat) :
    AllOutcomes (lift p n) (fun x => x.2 ≤ n) := by
  apply all_map
  induction p with
  | done x => exact Nat.le_refl _
  | ask i next ih => exact ih

theorem bind_bound {I A X Y : Type} (p : WorkProgram I A X)
    (next : X → WorkProgram I A Y) (a b : Nat)
    (hp : AllOutcomes p (fun x => x.2 ≤ a))
    (hn : ∀ x, AllOutcomes (next x) (fun y => y.2 ≤ b)) :
    AllOutcomes (bind p next) (fun y => y.2 ≤ a+b) := by
  apply all_bind
  apply all_mono _ hp
  intro x hx
  apply all_map
  exact all_mono _ (hn x.1) (fun y hy => Nat.add_le_add hx hy)

/-- Mapping the outcome preserves the complete fresh-tape cursor and trace.
The writer cannot suppress asks or move a later tape access earlier. -/
theorem eval_map_sequential {I A X Y : Type} (H : Nat → A)
    (p : Program I A X) (f : X → Y) (cursor : Nat) :
    (eval H (sequential (map f p) cursor)).2 =
      (f (eval H (sequential p cursor)).2.1,
        (eval H (sequential p cursor)).2.2) := by
  induction p generalizing cursor with
  | done x => rfl
  | ask i next ih => exact ih (H cursor) (cursor+1)

theorem eval_value {I A X : Type} (H : Nat → A) (p : WorkProgram I A X)
    (cursor : Nat) :
    (eval H (sequential (erase p) cursor)).2 =
      ((eval H (sequential p cursor)).2.1.1,
        (eval H (sequential p cursor)).2.2) :=
  eval_map_sequential H p Prod.fst cursor

theorem eval_bound {I A X : Type} (H : Nat → A) (p : WorkProgram I A X)
    (cursor B : Nat) (h : AllOutcomes p (fun x => x.2 ≤ B)) :
    (eval H (sequential p cursor)).2.1.2 ≤ B :=
  all_eval H _ _ (all_sequential p _ h cursor)

#print axioms map_map
#print axioms map_id
#print axioms erase_lift
#print axioms erase_bind
#print axioms all_map
#print axioms lift_bound
#print axioms bind_bound
#print axioms eval_map_sequential
#print axioms eval_value
#print axioms eval_bound
end AspisR1.ExtractorProgramWorkM10
