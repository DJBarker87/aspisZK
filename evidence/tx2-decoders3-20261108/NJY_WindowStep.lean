import NJQ_Words
import NJQ_CheckpointTrace
set_option autoImplicit false
noncomputable section
namespace NJY_WindowStep
open Aeneas Aeneas.Std Result NJI_CheckpointLoop
attribute [local instance] Classical.propDecidable
/-- Eight-byte window update after K041 split; no concrete recurrence reduction. -/
def write (before : Words) (k : Nat) (value : U64) : Words :=
 ⟨List.ofFn (fun j : Fin 8 => if j.val=k then value else NHY_ArrayExt.coord before j.val),by simp⟩

theorem coordinate (before : Words) (k : Nat) (value : U64) (j : Nat) (bound : j<8) :
 NHY_ArrayExt.coord (write before k value) j=
 (if j=k then value else NHY_ArrayExt.coord before j) := by
 unfold write NHY_ArrayExt.coord
 rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using bound)]
 simp only [Option.getD_some,List.getElem_ofFn]

/-- Native loop_window supplies this exact original window, including on Err. -/
theorem frame (b : Slice U8) (start : Nat) (fit : start+64≤b.val.length)
 (k : Nat) (bound : k<8) (before : Words) :
 Frame before
  (write before k (NJQ_Words.word b (start+8*k) (by omega)))
  (NJQ_Words.words b start fit) k := by
 intro j hj
 rw [coordinate before k _ j hj,NJQ_Words.coordinate b start fit k bound]

def step (before : Words) (k : Nat) (window : Array U8 8#usize) :
 core.result.Result Unit NJQ_CheckpointTrace.F × Words :=
 let value:=core.num.U64.from_le_bytes window
 (if value>capacity then .Err .InvalidMasterState else .Ok (),write before k value)

/-- Full write-before-rejection state and exact decision on the original word. -/
theorem source (b : Slice U8) (start : Nat) (fit : start+64≤b.val.length)
 (k : Nat) (bound : k<8) (before : Words) :
 step before k (NHY_NaturalReads.array b (start+8*k) 8#usize (by change start+8*k+8≤b.val.length;omega)) =
 (if NHY_ArrayExt.coord (NJQ_Words.words b start fit) k>capacity
  then .Err .InvalidMasterState else .Ok (),
  write before k (NHY_ArrayExt.coord (NJQ_Words.words b start fit) k)) := by
 rw [NJQ_Words.coordinate b start fit k bound]
 rfl
set_option pp.proofs false in
#print coordinate
#print axioms coordinate
set_option pp.proofs false in
#print frame
#print axioms frame
set_option pp.proofs false in
#print source
#print axioms source
end NJY_WindowStep
