import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_TupleContinuation

def uncurry4 {A B C D R : Type} (f : A → B → C → D → R) : A × B × C × D → R :=
  fun (a,b,c,d) => f a b c d

def curry4 {A B C D R : Type} (g : A × B × C × D → R) : A → B → C → D → R :=
  fun a b c d => g (a,b,c,d)

theorem curry_uncurry {A B C D R : Type} (f : A → B → C → D → R) :
    curry4 (uncurry4 f) = f := by
  rfl

theorem bind_tuple {A B C D R : Type} (g : A × B × C × D → Result R) :
    (fun a b c d => do let t ← ok (a,b,c,d);g t) = curry4 g := by
  rfl

#print axioms curry_uncurry
#print axioms bind_tuple
end NDD_TupleContinuation
