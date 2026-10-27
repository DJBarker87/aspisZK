import Std
namespace R1Z.PV_CB3_MonadicLoops
set_option autoImplicit false
universe u v
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

omit [LawfulMonad m] in
/-- Per-step source equality preserves the complete monadic result of every length. -/
theorem foldlM_congr {α σ : Type u} (f g : σ → α → m σ)
    (step : ∀ s a, f s a = g s a) (init : σ) (xs : List α) :
    xs.foldlM f init = xs.foldlM g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons, step, ih]

/-- Ordered loop concatenation retains effects and all failure/divergence outcomes. -/
theorem foldlM_append {α σ : Type u} (f : σ → α → m σ)
    (init : σ) (xs ys : List α) :
    (xs ++ ys).foldlM f init = (xs.foldlM f init >>= fun s => ys.foldlM f s) := by
  induction xs generalizing init with
  | nil => simp only [List.nil_append, List.foldlM_nil, pure_bind]
  | cons x xs ih =>
    simp only [List.cons_append, List.foldlM_cons, ih, bind_assoc]

/-- The source's nested row iteration can be flattened without reordering effects. -/
theorem foldlM_flatMap {α β σ : Type u} (f : σ → β → m σ) (row : α → List β)
    (init : σ) (xs : List α) :
    (xs.flatMap row).foldlM f init =
      xs.foldlM (fun s a => (row a).foldlM f s) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, foldlM_append, List.foldlM_cons, ih]

/-- A state abstraction proven at each step lifts to the entire Result, without
requiring the loop to succeed or prescribing its final value. -/
theorem foldlM_transport {α σ τ : Type u} (f : σ → α → m σ) (g : τ → α → m τ)
    (view : σ → τ)
    (step : ∀ s a, (f s a >>= fun t => pure (view t)) = g (view s) a)
    (init : σ) (xs : List α) :
    (xs.foldlM f init >>= fun s => pure (view s)) = xs.foldlM g (view init) := by
  induction xs generalizing init with
  | nil => simp only [List.foldlM_nil, pure_bind]
  | cons x xs ih =>
    simp only [List.foldlM_cons, bind_assoc, ih]
    rw [← step init x]
    simp only [bind_assoc, pure_bind]

#print axioms foldlM_congr
#print axioms foldlM_append
#print axioms foldlM_flatMap
#print axioms foldlM_transport
end R1Z.PV_CB3_MonadicLoops
