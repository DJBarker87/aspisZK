import NBB_Push
import NBB_RowTrace
import NBB_RowWitness
import NBB_Finish
import NBB_QueryTrace
import NBB_QueryWitness
import NBB_Cohort
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Frame
abbrev Row := Array U64 4#usize
abbrev Raw := NBB_Sweep.Raw
/-- Linked single-row writes on the SAME vector; no whole-vector frame is a premise. -/
inductive Writes : Nat → Nat → Raw → Raw → Prop
 | nil (start : Nat) (raw : Raw) : Writes start 0 raw raw
 | step {start count : Nat} {before mid : Raw}
   (prior : Writes start count before mid) (index : Usize) (row : Row)
   (atCursor : index.val=start+count) (inRange : index.val<mid.val.length) :
   Writes start (count+1) before (mid.set index row)

theorem set_frame (raw : Raw) (index : Usize) (row : Row) (j : Nat)
 (different : j≠index.val) :
 (raw.set index row).val[j]?=raw.val[j]? := by
 change (raw.val.set index.val row)[j]?=raw.val[j]?
 simp only [List.getElem?_set,if_neg different,if_neg (Ne.symm different)]

theorem length {start count : Nat} {before after : Raw}
 (trace : Writes start count before after) : after.val.length=before.val.length := by
 induction trace with
 | nil => rfl
 | step prior index row atCursor inRange ih =>
   change (List.set _ _ _).length=_
   rw [List.length_set,ih]

/-- A window of row writes retains every position outside that window. -/
theorem outside {start count : Nat} {before after : Raw}
 (trace : Writes start count before after) (j : Nat)
 (disjoint : j<start ∨ start+count≤j) : after.val[j]?=before.val[j]? := by
 induction trace with
 | nil => rfl
 | step prior index row atCursor inRange ih =>
   rw [set_frame _ _ _ _ (by omega)]
   exact ih (by omega)

/-- The native row stride is four U64 words. Disjoint row indices give
non-overlapping word windows, without evaluating a 64-row buffer. -/
theorem windows (i j : Nat) (different : i≠j) :
 4*i+4≤4*j ∨ 4*j+4≤4*i := by omega

#print axioms set_frame
#print axioms length
#print axioms outside
#print axioms windows
end NBF_Frame
