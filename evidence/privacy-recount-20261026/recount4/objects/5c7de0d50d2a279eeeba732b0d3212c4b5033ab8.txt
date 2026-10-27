import R1Z.ProverRwP6ResultMap
set_option autoImplicit false
namespace R1Z.ProverRwP6ArrayMap
open Aeneas Aeneas.Std Result
def map {A B : Type} {N : Usize} (f : A → B) (v : Array A N) : Array B N :=
  ⟨v.val.map f,by simp only [List.length_map,v.property]⟩
theorem index {A B : Type} {N : Usize} (f : A → B) (v : Array A N) (i : Usize) :
    Array.index_usize (map f v) i =
      ProverRwP6ResultMap.map f (Array.index_usize v i) := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq,map,List.getElem?_map]
  cases v.val[i.val]? <;> rfl
theorem set_map {A B : Type} {N : Usize} (f : A → B) (v : Array A N) (i : Usize) (a : A) :
    map f (Aeneas.Std.Array.set v i a) = Aeneas.Std.Array.set (map f v) i (f a) := by
  apply Subtype.ext
  simp only [map,Aeneas.Std.Array.set,List.map_set]
theorem repeat_map {A B : Type} (N : Usize) (f : A → B) (a : A) :
    map f (Array.repeat N a) = Array.repeat N (f a) := by
  apply Subtype.ext
  simp only [map,Array.repeat,List.map_replicate]
theorem roundtrip {A B : Type} {N : Usize} (f : A → B) (g : B → A)
    (inverse : ∀ a, g (f a) = a) (v : Array A N) : map g (map f v) = v := by
  apply Subtype.ext
  simp only [map,List.map_map]
  have he : g ∘ f = id := funext inverse
  rw [he,List.map_id]
#print axioms index
#print axioms set_map
#print axioms repeat_map
#print axioms roundtrip
end R1Z.ProverRwP6ArrayMap
