import NMT_345RawSelected
import NMT_345Raw_00
import NMT_345StepBase
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for txt in ["NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned", "NMT_345.rawSelected", "NMT_345.raw00", "NMT_345.tryStep"] do
  let decl := (txt.splitOn ".").foldl Name.str Name.anonymous
  let some info := env.find? decl | throwError "missing {decl}"
  let some body := info.value? | throwError "not a definition {decl}"
  for c in body.getUsedConstants do
   let s := c.toString
   if (s.splitOn "core.result.").length > 1 || (s.splitOn "FromSame").length > 1 then
    logInfo m!"{decl} uses {c}"
