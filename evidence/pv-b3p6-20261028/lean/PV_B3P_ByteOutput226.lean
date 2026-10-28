import Aeneas.Std
namespace PV_B3P_ByteOutput226
open Aeneas Aeneas.Std
set_option autoImplicit false
abbrev Chunks := Array (Array U8 64#usize) 23#usize

def flatten (a : Chunks) : List U8 := a.val.flatMap (fun x => x.val)

theorem flatten_length (a : Chunks) : (flatten a).length = 1472 := by
  have h64 : (64#usize).val = 64 := by rfl
  have h23 : (23#usize).val = 23 := by rfl
  have h : ∀ xs : List (Array U8 64#usize),
      (xs.flatMap (fun x => x.val)).length = xs.length * 64 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, Array.length_eq, List.length_cons]
      rw [ih, h64]
      omega
  have ha := Array.length_eq a
  have hf := h a.val
  change (a.val.flatMap (fun x => x.val)).length = 1472
  rw [hf, ha, h23]

def bytes (a : Chunks) (n : Usize) : alloc.vec.Vec U8 :=
  ⟨(flatten a).take n.val, by
    have hl := flatten_length a
    have hm : 1472 ≤ Usize.max := by scalar_tac
    simp only [List.length_take]
    omega⟩

theorem bytes_value (a : Chunks) (n : Usize) :
    (bytes a n).val = (flatten a).take n.val := rfl

theorem bytes_length (a : Chunks) (n : Usize) :
    (bytes a n).val.length = min n.val 1472 := by
  simp only [bytes_value, List.length_take, flatten_length]

#print axioms flatten_length
#print axioms bytes_value
#print axioms bytes_length
end PV_B3P_ByteOutput226
