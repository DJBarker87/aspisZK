import NBK_LiveStep
set_option autoImplicit false
namespace NBN_IteratorAssociation
open Aeneas Aeneas.Std Result
open AspisR1.S2K AspisR1.S2K.LoopStep
abbrev Rows := Array Digest 20#usize
abbrev Observation := Option (Nat × Digest) × Nat × Nat

def observe (out : Option (Usize × Digest) × Iter) : Observation :=
  (out.1.map (fun (k,d) => (k.val,d)),out.2.count.val,
    out.2.iter.slice.length - out.2.iter.i)

def projected (rows : Rows) (k : Usize) : Result Observation := do
  let step ← next (Iterator.cursor rows k)
  ok (observe step)

/-- Same index/row/next_index/remaining tuple as the native one-step K009 gate. -/
theorem next_row (rows : Rows) (k : Usize) (bound : k.val < 20) :
    projected rows k = ok
      (some (k.val,rows.val[k.val]'(by have := rows.property; scalar_tac)),
       k.val+1,19-k.val) := by
  rw [projected,Iterator.next_row rows k bound]
  simp only [bind_tc_ok,observe,Option.map_some,Iterator.cursor,
    Slice.length,Array.to_slice,rows.property]
  congr 2
  omega

theorem exhausted (rows : Rows) : projected rows 20#usize = ok (none,20,0) := by
  rw [projected,Iterator.exhausted]
  simp [observe,Iterator.cursor,Slice.length,Array.to_slice,rows.property]

#print axioms next_row
#print axioms exhausted
end NBN_IteratorAssociation
