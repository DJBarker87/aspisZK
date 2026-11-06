import NJB_StubLaws
open Lean Elab Command
#print FIq_Native.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal
#print AspisR1.FIv_NativeValue.Canon
#print AspisR1.FIv_NativeValue.decode
run_cmd do
 let env ← getEnv
 for (n, _) in env.constants.toList do
  let s := n.toString
  if (s.startsWith "AspisR1." && s.contains "decode" && (s.contains "inject" || s.contains "inj_")) || (s.startsWith "AspisR1.JFy_Absorption" || s.startsWith "AspisR1.FIx_Absorption" || s.startsWith "AspisR1.FIx_Builder." || s.startsWith "AspisR1.JFy_Active" || s.startsWith "AspisR1.FIw_Active" || (s.startsWith "AspisR1.JF" && s.contains "Active")) then
   elabCommand (← `(command| #check $(mkIdent n)))
