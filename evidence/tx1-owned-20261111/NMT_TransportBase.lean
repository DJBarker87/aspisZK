import NMT_tx1.Types
import CurrentCompactCallerTypesV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMT_Transport
open Aeneas Aeneas.Std

def arr {A B : Type} {n : Usize} (f : A → B) (x : Array A n) : Array B n :=
 ⟨x.val.map f, by simpa using x.property⟩
def vec {A B : Type} (f : A → B) (x : alloc.vec.Vec A) : alloc.vec.Vec B :=
 ⟨x.val.map f, by simpa using x.property⟩
theorem list_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : List A) : (xs.map f).map g=xs := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.map_cons,inverse,ih]
#print axioms list_inverse
@[simp] theorem arr_inverse {A B : Type} {n : Usize} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : Array A n) : arr g (arr f xs)=xs := by
 cases xs
 simp only [arr, list_inverse f g inverse]
@[simp] theorem vec_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : alloc.vec.Vec A) : vec g (vec f xs)=xs := by
 cases xs
 simp only [vec, list_inverse f g inverse]
#print axioms arr_inverse
#print axioms vec_inverse
end AspisR1.NMT_Transport
