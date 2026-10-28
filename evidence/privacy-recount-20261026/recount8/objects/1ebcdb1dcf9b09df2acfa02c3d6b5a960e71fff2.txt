import R1Z.PV_RunJoin_Vector44
import R1Z.ProverCommitFoldRange48
import R1Z.PV_RunJoin_FoldCell44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FourChildren44
open Aeneas Aeneas.Std Result
open ProverCommitWideOps48 PV_RunJoin_WideArithmetic44

theorem four {A : Type} (xs : Nat → A) :
    Array.make 4#usize [xs 0,xs 1,xs 2,xs 3] = ProverCommitArray49.array 4#usize xs := by
  apply Subtype.ext
  simp only [Array.make,ProverCommitArray49.array,List.ofFn_succ,List.ofFn_zero]
  rfl

theorem read (count : Usize) (q : Nat → Raw) (i : Usize) (hi : i.val < 256)
    (offset : Usize) (ho : offset.val ≤ 3) (bound : 4*i.val + 4 ≤ count.val) :
    Slice.index_usize (Array.to_slice (PV_RunJoin_FoldCell44.array count q))
      (Usize.wrapping_add (Usize.wrapping_mul 4#usize i) offset) =
      .ok (current (source (q (4*i.val + offset.val)))) := by
  have off := ProverCommitFoldRange48.offset_val i hi offset ho
  rw [PV_RunJoin_FoldCell44.array,PV_RunJoin_Vector44.read count
    (fun j => current (source (q j))) _ (by rw [off];omega),off]

theorem read_zero (count : Usize) (q : Nat → Raw) (i : Usize) (hi : i.val < 256)
    (bound : 4*i.val + 4 ≤ count.val) :
    Slice.index_usize (Array.to_slice (PV_RunJoin_FoldCell44.array count q))
      (Usize.wrapping_mul 4#usize i) = .ok (current (source (q (4*i.val)))) := by
  have off := ProverCommitFoldRange48.four_val i hi
  rw [PV_RunJoin_FoldCell44.array,PV_RunJoin_Vector44.read count
    (fun j => current (source (q j))) _ (by rw [off];omega),off]
#print axioms four
#print axioms read
#print axioms read_zero
end R1Z.PV_RunJoin_FourChildren44
