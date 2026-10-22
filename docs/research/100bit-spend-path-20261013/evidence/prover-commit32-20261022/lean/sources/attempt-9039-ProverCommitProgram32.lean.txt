import AspisR1Program32.Funs
import R1Z.ProverCommitPublication32
set_option autoImplicit false
namespace R1Z.ProverCommitProgram32
open Aeneas Aeneas.Std Result R1Z.ProverCommitPublication32
open AspisR1Program32

def byteOrder : List U8 → List U8 → I8
  | [], [] => 0#i8
  | [], _::_ => (-1)#i8
  | _::_, [] => 1#i8
  | a::xs, b::ys => if a<b then (-1)#i8 else if a>b then 1#i8 else byteOrder xs ys

/-- The extracted recursive comparator is lexicographic on all finite byte
strings, including empty strings and proper prefixes. -/
theorem byte_order_refines (fuel : Nat) (left right : Bytes) (pos : Usize)
    (hl : pos.val ≤ left.val.length) (hr : pos.val ≤ right.val.length)
    (hf : left.val.length-pos.val < fuel) :
    sim.owned32.byte_order left right pos =
      ok (byteOrder (left.val.drop pos.val) (right.val.drop pos.val)) := by
  induction fuel generalizing pos with
  | zero => omega
  | succ fuel ih =>
    rw [sim.owned32.byte_order]
    by_cases endl : pos = alloc.vec.Vec.len left
    · have hp : pos.val = left.val.length := congrArg UScalar.val endl
      simp only [if_pos endl,List.drop_eq_nil_of_le (by omega : left.val.length ≤ pos.val)]
      by_cases endr : pos = alloc.vec.Vec.len right
      · have hpr : pos.val = right.val.length := congrArg UScalar.val endr
        simp only [if_pos endr,List.drop_eq_nil_of_le (by omega : right.val.length ≤ pos.val),byteOrder]
      · have more : pos.val < right.val.length := by
          have ne : pos.val ≠ right.val.length := by
            intro eq;apply endr;apply UScalar.eq_of_val_eq;exact eq
          omega
        rw [List.drop_eq_getElem_cons more]
        simp only [if_neg endr,byteOrder]
    · have morel : pos.val < left.val.length := by
        have ne : pos.val ≠ left.val.length := by
          intro eq;apply endl;apply UScalar.eq_of_val_eq;exact eq
        omega
      simp only [if_neg endl]
      by_cases endr : pos = alloc.vec.Vec.len right
      · have hp : pos.val = right.val.length := congrArg UScalar.val endr
        rw [List.drop_eq_getElem_cons morel]
        simp only [if_pos endr,List.drop_eq_nil_of_le (by omega : right.val.length ≤ pos.val),byteOrder]
      · have morer : pos.val < right.val.length := by
          have ne : pos.val ≠ right.val.length := by
            intro eq;apply endr;apply UScalar.eq_of_val_eq;exact eq
          omega
        obtain ⟨a,ha,hea⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec left pos morel)
        obtain ⟨b,hb,heb⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec right pos morer)
        have dl : left.val.drop pos.val = a :: left.val.drop (pos.val+1) := by
          rw [hea];exact List.drop_eq_getElem_cons morel
        have dr : right.val.drop pos.val = b :: right.val.drop (pos.val+1) := by
          rw [heb];exact List.drop_eq_getElem_cons morer
        have step := next_cursor left pos morel
        have tail := ih (Usize.wrapping_add pos 1#usize) (by omega) (by omega) (by omega)
        rw [step] at tail
        simp only [if_neg endr,alloc.vec.Vec.index_slice_index,ha,hb,bind_tc_ok,dl,dr,byteOrder]
        by_cases lt : a<b
        · simp only [lt,if_true]
        · simp only [lt,if_false]
          by_cases gt : a>b
          · simp only [gt,if_true]
          · simp only [gt,if_false,lift,bind_tc_ok,tail]

#print axioms byte_order_refines
end R1Z.ProverCommitProgram32
