import Aeneas
set_option autoImplicit false
namespace PV_B1_Transport
open Aeneas Aeneas.Std Result

def resultMap {A B : Type} (f : A → B) : Result A → Result B
  | ok a => ok (f a)
  | fail e => fail e
  | div => div

theorem result_bind {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
    resultMap f (r >>= k) = (r >>= fun a => resultMap f (k a)) := by
  cases r <;> rfl

theorem result_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    resultMap g (resultMap f r) = resultMap (g ∘ f) r := by
  cases r <;> rfl

theorem result_identity {A : Type} (r : Result A) : resultMap id r = r := by
  cases r <;> rfl

theorem result_roundtrip {A B : Type} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a)=a) (r : Result A) : resultMap g (resultMap f r) = r := by
  cases r with
  | ok a => simp only [resultMap,h]
  | fail e => rfl
  | div => rfl

def arrayMap {A B : Type} {N : Usize} (f : A → B) (v : Array A N) : Array B N :=
  ⟨v.val.map f,by simp only [List.length_map,v.property]⟩

def sliceMap {A B : Type} (f : A → B) (v : Slice A) : Slice B :=
  ⟨v.val.map f,by simpa only [List.length_map] using v.property⟩

theorem array_index {A B : Type} {N : Usize} (f : A → B) (v : Array A N) (i : Usize) :
    Array.index_usize (arrayMap f v) i = resultMap f (Array.index_usize v i) := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq,arrayMap,List.getElem?_map]
  cases v.val[i.val]? <;> rfl

theorem slice_index {A B : Type} (f : A → B) (v : Slice A) (i : Usize) :
    Slice.index_usize (sliceMap f v) i = resultMap f (Slice.index_usize v i) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,sliceMap,List.getElem?_map]
  cases v.val[i.val]? <;> rfl

theorem slice_length {A B : Type} (f : A → B) (v : Slice A) :
    Slice.len (sliceMap f v) = Slice.len v := by
  apply UScalar.eq_of_val_eq
  simp only [Slice.len_val,Slice.length,sliceMap,List.length_map]

theorem array_set {A B : Type} {N : Usize} (f : A → B) (v : Array A N) (i : Usize) (a : A) :
    arrayMap f (Aeneas.Std.Array.set v i a) = Aeneas.Std.Array.set (arrayMap f v) i (f a) := by
  apply Subtype.ext
  simp only [arrayMap,Aeneas.Std.Array.set,List.map_set]

theorem array_repeat {A B : Type} (N : Usize) (f : A → B) (a : A) :
    arrayMap f (Array.repeat N a) = Array.repeat N (f a) := by
  apply Subtype.ext
  simp only [arrayMap,Array.repeat,List.map_replicate]

theorem array_roundtrip {A B : Type} {N : Usize} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a)=a) (v : Array A N) : arrayMap g (arrayMap f v)=v := by
  apply Subtype.ext
  simp only [arrayMap,List.map_map]
  have he : g ∘ f=id := funext h
  rw [he,List.map_id]

theorem slice_roundtrip {A B : Type} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a)=a) (v : Slice A) : sliceMap g (sliceMap f v)=v := by
  apply Subtype.ext
  simp only [sliceMap,List.map_map]
  have he : g ∘ f=id := funext h
  rw [he,List.map_id]
#print axioms result_bind
#print axioms result_comp
#print axioms result_identity
#print axioms result_roundtrip
#print axioms array_index
#print axioms slice_index
#print axioms slice_length
#print axioms array_set
#print axioms array_repeat
#print axioms array_roundtrip
#print axioms slice_roundtrip
end PV_B1_Transport
