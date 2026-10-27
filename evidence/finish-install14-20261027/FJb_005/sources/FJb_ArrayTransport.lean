import FJa_PoseidonPow5
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ArrayTransport
open Aeneas Aeneas.Std Result
open FIv_Map (map)
open FIv_NativeArithmetic (NQ PQ qm)
def array {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f,by simp only [List.length_map,a.property]⟩
theorem index {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) :
    Array.index_usize (array f a) i=map f (Array.index_usize a i) := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq,array,List.getElem?_map]
  cases a.val[i.val]? <;> rfl
theorem update {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) (x : A) :
    Array.update (array f a) i (f x)=map (array f) (Array.update a i x) := by
  simp only [Array.update,Array.getElem?_Usize_eq,array,List.getElem?_map]
  cases h : a.val[i.val]? with
  | none => rfl
  | some y =>
    simp only [Option.map_some,map]
    congr 1
    apply Subtype.ext
    exact (List.map_set f a.val i.val x).symm
#print axioms index
#print axioms update
end AspisR1.FJb_ArrayTransport
end
