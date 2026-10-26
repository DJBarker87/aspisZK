import Mathlib.Tactic

/-! Small-step writer accounting. `work` counts primitive inspections,
comparisons, field operations, copies and allocation events. Fixed-width
representation constants are applied separately. This library certifies
composition, not the adequacy of an arbitrary primitive's chosen charge. -/
set_option autoImplicit false
namespace AspisR1.ExtractorWorkMonad

abbrev Work (A : Type) := A × Nat

def pure {A : Type} (a : A) : Work A := (a, 0)
def tick (n : Nat) : Work Unit := ((), n)
def bind {A B : Type} (x : Work A) (f : A → Work B) : Work B :=
  let y := f x.1
  (y.1, x.2 + y.2)
def map {A B : Type} (f : A → B) (x : Work A) : Work B := (f x.1, x.2)

theorem bind_value {A B : Type} (x : Work A) (f : A → Work B) :
    (bind x f).1 = (f x.1).1 := rfl

theorem bind_bound {A B : Type} (x : Work A) (f : A → Work B) (a b : Nat)
    (hx : x.2 ≤ a) (hf : ∀ v, (f v).2 ≤ b) :
    (bind x f).2 ≤ a + b := Nat.add_le_add hx (hf x.1)

def foldl {A S : Type} (f : S → A → Work S) : S → List A → Work S
  | s, [] => pure s
  | s, a :: rest => bind (f s a) (fun s' => foldl f s' rest)

theorem foldl_value {A S : Type} (f : S → A → Work S) (s : S) (xs : List A) :
    (foldl f s xs).1 = xs.foldl (fun s a => (f s a).1) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact ih _

/-- Uniform over every intermediate state, including failed retry states. -/
theorem foldl_bound {A S : Type} (f : S → A → Work S) (xs : List A)
    (c : Nat) (h : ∀ s a, a ∈ xs → (f s a).2 ≤ c) (s : S) :
    (foldl f s xs).2 ≤ xs.length * c := by
  induction xs generalizing s with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    have hh := h s a List.mem_cons_self
    have ht := ih (fun s a ha => h s a (List.mem_cons_of_mem _ ha)) (f s a).1
    change (f s a).2 + _ ≤ _
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      Nat.add_le_add hh ht

theorem foldl_with_initial_bound {A S : Type} (f : S → A → Work S)
    (xs : List A) (x : Work S) (c d : Nat) (hx : x.2 ≤ d)
    (h : ∀ s a, a ∈ xs → (f s a).2 ≤ c) :
    (bind x (fun s => foldl f s xs)).2 ≤ xs.length * c + d := by
  have ht := foldl_bound f xs c h x.1
  change x.2 + (foldl f x.1 xs).2 ≤ _
  omega

def forLoop {S : Type} (fuel : Nat) (f : S → Nat → Work S) (s : S) : Work S :=
  foldl f s (List.range fuel)

theorem forLoop_value {S : Type} (fuel : Nat) (f : S → Nat → Work S) (s : S) :
    (forLoop fuel f s).1 = (List.range fuel).foldl (fun s i => (f s i).1) s :=
  foldl_value _ _ _

theorem forLoop_bound {S : Type} (fuel c : Nat) (f : S → Nat → Work S)
    (h : ∀ s i, i < fuel → (f s i).2 ≤ c) (s : S) :
    (forLoop fuel f s).2 ≤ fuel * c := by
  simpa only [forLoop, List.length_range] using
    foldl_bound f (List.range fuel) c (fun s i hi => h s i (List.mem_range.mp hi)) s

/-- An explicitly bounded retry loop. Aborting steps still incur their work;
once stopped, later iterations are skipped, never silently reattempted. -/
def retryStep {S : Type} (f : S → Nat → Work (Option S))
    (s : Option S) (i : Nat) : Work (Option S) :=
  match s with
  | none => pure none
  | some s => f s i

theorem retry_bound {S : Type} (fuel c : Nat)
    (f : S → Nat → Work (Option S)) (h : ∀ s i, i < fuel → (f s i).2 ≤ c)
    (s : Option S) : (forLoop fuel (retryStep f) s).2 ≤ fuel * c := by
  apply forLoop_bound
  intro s i hi
  cases s with
  | none => exact Nat.zero_le _
  | some s => exact h s i hi

/-- Allocation events are charged cumulatively. With at most `initial`
preexisting live fixed-width elements, this also bounds peak live bits.
This does not assert a constant-size representation for unrestricted Nats. -/
theorem representation_bound (live initial allocated width : Nat)
    (h : live ≤ initial + allocated) :
    live * width ≤ (initial + allocated) * width := Nat.mul_le_mul_right _ h

#print axioms bind_value
#print axioms bind_bound
#print axioms foldl_value
#print axioms foldl_bound
#print axioms foldl_with_initial_bound
#print axioms forLoop_value
#print axioms forLoop_bound
#print axioms retry_bound
#print axioms representation_bound
end AspisR1.ExtractorWorkMonad
