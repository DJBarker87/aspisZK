import NGX_COMBINED_IMPORT
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for entry in env.constants.toList do
  let n := entry.1
  let s := n.toString
  if (s.startsWith "AspisR1PublicPreparation." && (s.endsWith ".fields_loop.body" || s.endsWith ".semantic" || s.endsWith ".public_transcript" || s.endsWith ".begin" || s.endsWith ".begin5" || s.endsWith ".begin10")) || s.endsWith ".Iter" then
   if s.startsWith "AspisR1PublicPreparation." || s.startsWith "Aeneas.Std.core.slice" then
    logInfo m!"NHG_OWNER {n}: {entry.2.type}"
#print AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop.body
#check Aeneas.Std.alloc.vec.Vec.extend_from_slice
#check Aeneas.Std.core.slice.iter.IteratorSliceIter.next
#print AspisR1PublicPreparation.r1_semantic.public_transcript
