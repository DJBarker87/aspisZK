import NNH_ValidateSdkPort
open Aeneas Aeneas.Std AdapterRw
#print core.option.Option.Insts.CoreCmpPartialEqOption
#print core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
open Lean in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  let s := n.toString
  if (s.splitOn ".slice.cmp.").length>1 && (s.splitOn "._").length=1 then
   logInfo m!"{n}"
