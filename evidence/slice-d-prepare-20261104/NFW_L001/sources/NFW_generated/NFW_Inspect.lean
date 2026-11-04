import NFQ_STAGE2_IMPORT
import NFS_QueryLoopRoot
import Lean
open Lean Elab Command
run_cmd do
 for (n, ci) in (← getEnv).constants.toList do
  let s := n.toString
  if (s.endsWith ".powers" || s.endsWith ".powers_loop" || s.endsWith ".Prepared.new" || s.endsWith ".candidate.prepare" || s.endsWith ".verify_observed") && !s.startsWith "_" then
   logInfo m!"{n} : {ci.type}"
