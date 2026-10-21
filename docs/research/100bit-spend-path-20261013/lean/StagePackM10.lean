import AbstractStageSpecM10

/-! Package component laws while all functions remain abstract variables.
This avoids kernel comparison of two concrete structure field projections. -/
set_option autoImplicit false
namespace AspisR1.StagePackM10
open AbstractStageSpecM10

def pack {A B : Type} (f : A → Option B) (I : A → Prop) (J : B → Prop)
    (F : Nat → Nat) (r : A → Option B × Nat)
    (hv : ∀ a, (r a).1 = f a)
    (hw : ∀ L a, I a → (r a).2 ≤ F L)
    (ho : ∀ a b, I a → (r a).1 = some b → J b) : StageSpec f I J F :=
  ⟨r,hv,hw,ho⟩

/-- All-input bounds can be installed at every abstract log length. -/
theorem const_work {A B : Type} (r : A → Option B × Nat) (C : Nat)
    (h : ∀ a, (r a).2 ≤ C) : ∀ L : Nat, ∀ a, True → (r a).2 ≤ (fun _ => C) L :=
  fun _ a _ => h a

theorem true_output {A B : Type} (r : A → Option B × Nat) :
    ∀ a b, True → (r a).1 = some b → True := fun _ _ _ _ => True.intro

#print axioms const_work
#print axioms true_output
end AspisR1.StagePackM10
