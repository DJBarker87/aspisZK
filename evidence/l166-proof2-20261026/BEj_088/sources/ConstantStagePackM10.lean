import AbstractStageSpecM10

set_option autoImplicit false
namespace AspisR1.ConstantStagePackM10
open AbstractStageSpecM10

def pack {A B : Type} (f : A → Option B) (J : B → Prop) (C : Nat)
    (r : A → Option B × Nat) (hv : ∀ a, (r a).1 = f a)
    (hw : ∀ a, (r a).2 ≤ C)
    (ho : ∀ a b, (r a).1 = some b → J b) :
    StageSpec f (fun _ => True) J (fun _ => C) :=
  ⟨r,hv,fun _ a _ => hw a,fun a b _ hb => ho a b hb⟩

theorem run_value {A B : Type} (f : A → Option B) (J : B → Prop) (C : Nat)
    (r : A → Option B × Nat) (hv : ∀ a, (r a).1 = f a)
    (hw : ∀ a, (r a).2 ≤ C) (ho : ∀ a b, (r a).1 = some b → J b) (a : A) :
    ((pack f J C r hv hw ho).run a).1 = f a := hv a

#print axioms run_value
end AspisR1.ConstantStagePackM10
