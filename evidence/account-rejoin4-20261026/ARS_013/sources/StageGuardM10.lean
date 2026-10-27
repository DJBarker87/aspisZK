import AbstractStageSpecM10

set_option autoImplicit false
namespace AspisR1.StageGuardM10
open AbstractStageSpecM10

def guard {A B : Type} {f : A → Option B} {I : A → Prop} {J : B → Prop}
    {F : Nat → Nat} (P : Prop) (s : StageSpec f I J F) :
    StageSpec f (fun a => I a ∧ P) (fun b => J b ∧ P) F where
  run := s.run
  value := s.value
  work L a ha := s.work L a ha.1
  invariant a b ha hb := ⟨s.invariant a b ha.1 hb,ha.2⟩

theorem value {A B : Type} {f : A → Option B} {I : A → Prop} {J : B → Prop}
    {F : Nat → Nat} (P : Prop) (s : StageSpec f I J F) (a : A) :
    ((guard P s).run a).1 = f a := (guard P s).value a

#print axioms value
end AspisR1.StageGuardM10
