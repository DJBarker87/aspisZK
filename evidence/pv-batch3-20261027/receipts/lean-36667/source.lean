import Aeneas.Std
namespace PV_B3_ArrayCarrier
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def resultMap {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def arrayMap {A B : Type} {n : Usize} (f : A → B) (a : Array A n) : Array B n :=
  ⟨a.val.map f, by rw [List.length_map, a.property]⟩

theorem index {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) :
    Array.index_usize (arrayMap f a) i = resultMap f (Array.index_usize a i) := by
  unfold Array.index_usize
  change (match (a.val.map f)[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = resultMap f (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x)
  rw [List.getElem?_map]
  cases h : a.val[i.val]? <;> rfl

theorem set {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) (x : A) :
    arrayMap f (Aeneas.Std.Array.set a i x) =
      Aeneas.Std.Array.set (arrayMap f a) i (f x) := by
  apply Subtype.ext
  change (a.val.set i.val x).map f = (a.val.map f).set i.val (f x)
  simp only [List.map_set]

theorem map_comp {A B C : Type} {n : Usize} (f : A → B) (g : B → C) (a : Array A n) :
    arrayMap g (arrayMap f a) = arrayMap (fun x => g (f x)) a := by
  apply Subtype.ext
  simp only [arrayMap, List.map_map, Function.comp_def]

theorem map_id {A : Type} {n : Usize} (a : Array A n) : arrayMap (fun x => x) a = a := by
  apply Subtype.ext
  simp only [arrayMap, List.map_id]

theorem inverse {A B : Type} {n : Usize} (f : A → B) (g : B → A)
    (h : ∀ x, g (f x) = x) (a : Array A n) : arrayMap g (arrayMap f a) = a := by
  rw [map_comp]
  have hf : (fun x => g (f x)) = (fun x => x) := funext h
  rw [hf]
  exact map_id a

#print axioms resultMap
#print axioms arrayMap
#print axioms index
#print axioms set
#print axioms map_comp
#print axioms map_id
#print axioms inverse
end PV_B3_ArrayCarrier
