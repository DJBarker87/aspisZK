import NJQ_Read
import NHY_ArrayExt
set_option autoImplicit false
noncomputable section
namespace NJQ_Words
open Aeneas Aeneas.Std Result
abbrev Words := Array U64 8#usize

def word (b : Slice U8) (start : Nat) (fit : start+8≤b.val.length) : U64 :=
 core.num.U64.from_le_bytes (NHY_NaturalReads.array b start 8#usize fit)

def words (b : Slice U8) (start : Nat) (fit : start+64≤b.val.length) : Words :=
 ⟨List.ofFn (fun j : Fin 8 => word b (start+8*j.val) (by have := j.isLt;omega)),by simp⟩

/-- Every loop step consumes the SAME original eight-byte window. -/
theorem coordinate (b : Slice U8) (start : Nat) (fit : start+64≤b.val.length)
 (k : Nat) (bound : k<8) :
 NHY_ArrayExt.coord (words b start fit) k =
 word b (start+8*k) (by omega) := by
 unfold words NHY_ArrayExt.coord
 rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using bound)]
 simp only [Option.getD_some,List.getElem_ofFn]

/-- Exact library call/byte argument on every entered step, including a rejecting one. -/
theorem step_argument (b : Slice U8) (start : Usize) (k : Usize)
 (width : start.val+64≤b.val.length) (bound : k.val<8)
 (offset : Usize) (same : offset.val=start.val+8*k.val) :
 NJQ_Read.read b offset 8#usize=
 ok (NHY_NaturalReads.array b (start.val+8*k.val) 8#usize (by change start.val+8*k.val+8≤b.val.length;omega)) := by
 have h := NJQ_Read.value b offset 8#usize (by change offset.val+8≤b.val.length;omega)
 simpa only [same] using h

#print axioms coordinate
#print axioms step_argument
end NJQ_Words
