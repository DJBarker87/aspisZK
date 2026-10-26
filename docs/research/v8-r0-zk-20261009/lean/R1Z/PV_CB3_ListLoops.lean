import Std
namespace R1Z.PV_CB3_ListLoops
set_option autoImplicit false

/-- Replacing a loop body by a pointwise equal body preserves the whole loop,
including its accumulator. Used for the per-step P6 route, without fixing outputs. -/
theorem foldl_congr {α σ : Type} (f g : σ → α → σ)
    (step : ∀ s a, f s a = g s a) (init : σ) (xs : List α) :
    xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, step, ih]

/-- Four ordered operations per row compose into the flattened operand loop. -/
theorem foldl_flatMap {α β σ : Type} (f : σ → β → σ) (row : α → List β)
    (init : σ) (xs : List α) :
    (xs.flatMap row).foldl f init =
      xs.foldl (fun s a => (row a).foldl f s) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, ih]

/-- Accumulator abstraction lifts a checked per-step equality to any loop length. -/
theorem foldl_transport {α σ τ : Type} (f : σ → α → σ) (g : τ → α → τ)
    (view : σ → τ) (step : ∀ s a, view (f s a) = g (view s) a)
    (init : σ) (xs : List α) :
    view (xs.foldl f init) = xs.foldl g (view init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, step]

#print axioms foldl_congr
#print axioms foldl_flatMap
#print axioms foldl_transport
end R1Z.PV_CB3_ListLoops
