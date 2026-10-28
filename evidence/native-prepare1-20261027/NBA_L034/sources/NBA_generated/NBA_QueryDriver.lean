import NBA_ArrayEight
import Query31ConcreteMaterializedSchedule
set_option autoImplicit false
namespace AspisR1.NBA_QueryDriver
open Aeneas Aeneas.Std Result
open AspisR1Query31Transcript
abbrev State := aspis_core.r0_transcript.QueryScan
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize
abbrev Out := core.result.Result (Array U32 22#usize × Bytes32) aspis_core.transcript.QuerySampleError

def walk (scan : State → Bytes32 → Result (Bool×State)) (advances : Blocks)
    (fallback : Usize) : List (Bytes32×Usize) → State → Result Out
  | [],s => finishAdvance advances fallback s
  | (block,index)::xs,s => do
      let (stop,next) ← scan s block
      if stop then finishAdvance advances index next else walk scan advances fallback xs next

/-- First-stop driver with the SAME original arrays and default advance7.
This is a generic full Result equality, including decode and finish errors. -/
theorem source (scan : State → Bytes32 → Result (Bool×State)) (s : State)
    (blocks advances : Blocks) :
    queries_from_pairs_with_scan scan s blocks advances=
      walk scan advances 7#usize (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]) s := by
  have values := NBA_ArrayEight.literal blocks
  have r0 := NBA_ArrayEight.read blocks 0#usize (by decide)
  have r1 := NBA_ArrayEight.read blocks 1#usize (by decide)
  have r2 := NBA_ArrayEight.read blocks 2#usize (by decide)
  have r3 := NBA_ArrayEight.read blocks 3#usize (by decide)
  have r4 := NBA_ArrayEight.read blocks 4#usize (by decide)
  have r5 := NBA_ArrayEight.read blocks 5#usize (by decide)
  have r6 := NBA_ArrayEight.read blocks 6#usize (by decide)
  have r7 := NBA_ArrayEight.read blocks 7#usize (by decide)
  rw [values]
  simp only [queries_from_pairs_with_scan,walk,List.zip_cons_cons,List.zip_nil_left,
    r0,r1,r2,r3,r4,r5,r6,r7,bind_tc_ok,finishAdvance,ite_self]

#print axioms source
end AspisR1.NBA_QueryDriver
