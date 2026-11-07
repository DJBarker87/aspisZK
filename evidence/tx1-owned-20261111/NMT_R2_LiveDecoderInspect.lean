import NMT_345Decoder
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let targets := ["AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1",
   "AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1",
   "AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1"].map
   (fun s => (s.splitOn ".").foldl Name.str Name.anonymous)
 for (n, info) in env.constants.toList do
  let s := n.toString
  if (s.splitOn "_proof").length == 1 && (s.splitOn "_simp").length == 1 then
   match info with
   | .thmInfo d =>
    if targets.any (fun t => d.type.getUsedConstants.contains t) then logInfo m!"{n}: {d.type}"
   | _ => pure ()
