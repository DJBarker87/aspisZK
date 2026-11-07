import NMT_345EqByte
import NMT_345Distinct
import Lean
open Lean Elab Command
#print Aeneas.Std.core.cmp.PartialEqU8
#print Aeneas.Std.WP.theta
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if (s.startsWith "NGL_DistinctInduction.outer." || s.startsWith "NGL_DistinctInduction.inner.") &&
     ((s.splitOn ".eq_").length > 1) && (s.splitOn "_proof").length == 1 then
   logInfo m!"{n}: {info.type}"
