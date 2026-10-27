import FIv_Arithmetic
set_option autoImplicit false
namespace AspisR1.JGb_ArrayMap
open Aeneas Aeneas.Std Result
open FIv_Map (map)
def array {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
theorem read {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) :
    map f (Array.index_usize a i)=Array.index_usize (array f a) i := by
  unfold Array.index_usize
  simp only [array,List.length_map]
  split
  · simp only [List.getElem_map,map]
  · rfl
#print axioms read
end AspisR1.JGb_ArrayMap
