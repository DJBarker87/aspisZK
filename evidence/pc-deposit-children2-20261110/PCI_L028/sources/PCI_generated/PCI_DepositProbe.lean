import NFY_Part005
import PCF_ResultAssoc
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for n in ["Aeneas.Std.Slice.Insts.CoreCmpPartialEqArray.ne", "AspisR1AdapterReconstruct.Slice.Insts.CoreCmpPartialEqArray.ne", "Aeneas.Std.core.option.Option.ok_or", "AspisR1AdapterReconstruct.core.option.Option.ok_or", "Aeneas.Std.core.result.Result.map_err", "AspisR1AdapterReconstruct.core.result.Result.map_err"] do
  match env.find? n.toName with
  | none => logInfo m!"MISSING {n}"
  | some c => logInfo m!"FOUND {n}: {c.type}"
