import Aeneas.Std
namespace PV_B3P_Ordered227
open Aeneas Aeneas.Std
set_option autoImplicit false

/-- An ordered loop body, including its complete failure/divergence Result. -/
def fold {α β : Type} (step : α → β → Result α) : List β → α → Result α
  | [], state => .ok state
  | x::xs, state => do
    let next ← step state x
    fold step xs next

theorem bind_assoc {α β γ : Type} (r : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (do let y ← (do let x ← r; f x); g y) = (do let x ← r; let y ← f x; g y) := by
  cases r <;> rfl

theorem append {α β : Type} (step : α → β → Result α)
    (xs ys : List β) (state : α) :
    fold step (xs ++ ys) state = (do let next ← fold step xs state; fold step ys next) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,fold]
    rw [bind_assoc]
    cases step state x with
    | ok next => exact ih next
    | fail e => rfl
    | div => rfl

def ranges {α β : Type} (step : α → β → Result α) : List (List β) → α → Result α
  | [], state => .ok state
  | xs::rest, state => do
    let next ← fold step xs state
    ranges step rest next

theorem flatten {α β : Type} (step : α → β → Result α)
    (groups : List (List β)) (state : α) :
    ranges step groups state = fold step groups.flatten state := by
  induction groups generalizing state with
  | nil => rfl
  | cons xs rest ih =>
    simp only [List.flatten_cons,ranges,append]
    cases fold step xs state with
    | ok next => exact ih next
    | fail e => rfl
    | div => rfl

/-- Splitting an index interval retains order and the incoming accumulator. -/
theorem interval_split {α : Type} (step : α → Nat → Result α)
    (start left right : Nat) (state : α) :
    fold step (List.range' start (left+right)) state = (do
      let next ← fold step (List.range' start left) state
      fold step (List.range' (start+left) right) next) := by
  have h := (List.range'_append start left right 1).symm
  simpa only [Nat.one_mul] using congrArg (fun xs => fold step xs state) h |>.trans (append step (List.range' start left) (List.range' (start+left) right) state)

/-- Moving an immutable copy ahead of a Result computation preserves all tags. -/
theorem pure_copy {α β γ : Type} (source : α) (copy : α → β)
    (r : Result γ) :
    (do let value ← r; .ok (copy source,value)) =
      (let copied := copy source; do let value ← r; .ok (copied,value)) := rfl

/-- Delayed private writes preserve call/error order when later calls use snapshots.
No state is returned on failure or divergence. -/
theorem delayed_writes {σ α β γ δ : Type} (state : σ)
    (first : Result α) (second : Result β) (third : Result γ) (fourth : Result δ)
    (put0 : σ → α → σ) (put1 : σ → β → σ)
    (put2 : σ → γ → σ) (put3 : σ → δ → σ) :
    (do
      let a ← first
      let s0 := put0 state a
      let b ← second
      let s1 := put1 s0 b
      let c ← third
      let s2 := put2 s1 c
      let d ← fourth
      .ok (put3 s2 d)) = (do
      let a ← first
      let b ← second
      let c ← third
      let d ← fourth
      .ok (put3 (put2 (put1 (put0 state a) b) c) d)) := rfl

#print axioms bind_assoc
#print axioms append
#print axioms flatten
#print axioms interval_split
#print axioms pure_copy
#print axioms delayed_writes
end PV_B3P_Ordered227
