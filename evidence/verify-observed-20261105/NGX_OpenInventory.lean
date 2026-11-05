import NGX_COMBINED_IMPORT
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for entry in env.constants.toList do
  let n := entry.1
  let ci := entry.2
  let s := n.toString
  if s.endsWith ".public_bytes" || s.endsWith ".decode_k" ||
     s.endsWith ".semantic_boundary" || s.endsWith ".semantic_value" ||
     s.endsWith ".selected_binary_weight" || s.endsWith ".link_weight" ||
     s.endsWith ".bounded_append_carry" || s.endsWith ".selected_claim" then
   logInfo m!"NGX_OPEN_OWNER {n}: {ci.type}"
