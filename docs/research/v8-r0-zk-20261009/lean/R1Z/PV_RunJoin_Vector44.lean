import R1Z.PV_RunJoin_WideArithmetic44
import R1Z.ProverCommitArray49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_Vector44
open Aeneas Aeneas.Std Result
variable {A : Type}

theorem read (size : Usize) (xs : Nat → A) (i : Usize) (bound : i.val < size.val) :
    Slice.index_usize (Array.to_slice (ProverCommitArray49.array size xs)) i = .ok (xs i.val) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,Array.to_slice,
    ProverCommitArray49.array,List.getElem?_ofFn,bound,↓reduceDIte]

theorem push (out : alloc.vec.Vec A) (a : A) (room : out.length + 1 ≤ Usize.max) :
    ∃ next, alloc.vec.Vec.push out a = .ok next ∧ next.val = out.val ++ [a] := by
  exact ⟨⟨out.val ++ [a],by simpa only [List.length_append,List.length_singleton] using room⟩,by
    simp only [alloc.vec.Vec.push,dif_pos room],rfl⟩

#print axioms read
#print axioms push
end R1Z.PV_RunJoin_Vector44
