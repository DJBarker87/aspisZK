import NDO_JHe_CurrentWriterImage
set_option autoImplicit false
namespace AspisR1.JHl_ByteBlocks
open Aeneas Aeneas.Std

theorem range_blocks {A : Type} (xs : List A) (width n : Nat) :
    ((List.range n).map (fun j => (xs.drop (width*j)).take width)).flatten=xs.take (width*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.flatten_append,ih]
    simp only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
    rw [Nat.mul_succ,List.take_add]
#print axioms range_blocks

theorem ofFn_map {A : Type} (n : Nat) (f : Nat → A) :
    List.ofFn (fun j : Fin n => f j.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
#print axioms ofFn_map

theorem blocks {A : Type} (xs : List A) (start width n : Nat) :
    (List.ofFn (fun j : Fin n => (xs.drop (start+width*j.val)).take width)).flatten=
      (xs.drop start).take (width*n) := by
  rw [ofFn_map n (fun j => (xs.drop (start+width*j)).take width)]
  have h := range_blocks (xs.drop start) width n
  simpa only [List.drop_drop,Nat.add_comm] using h
#print axioms blocks
end AspisR1.JHl_ByteBlocks
