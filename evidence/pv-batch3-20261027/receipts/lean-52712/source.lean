import R1Z.ProverCommitArrayIndex25
namespace PV_B3_MaskArray
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem repeat_read {α : Type} (n : Usize) (x : α) (i : Usize)
    (hi : i.val < n.val) : Array.index_usize (Array.repeat n x) i = ok x := by
  rw [R1Z.ProverCommitArrayIndex25.array_index_usize_ok (Array.repeat n x) i hi]
  simp only [Array.repeat, List.getElem_replicate]

theorem producer_zero (i : Usize) (hi : i.val < 1024) :
    Array.index_usize (Array.repeat 1024#usize 0#u8) i = ok 0#u8 :=
  repeat_read 1024#usize 0#u8 i hi

theorem mask_zero (i : Usize) (hi : i.val < 64) :
    Array.index_usize (Array.repeat 64#usize 0#u16) i = ok 0#u16 :=
  repeat_read 64#usize 0#u16 i hi

#print axioms repeat_read
#print axioms producer_zero
#print axioms mask_zero
end PV_B3_MaskArray
