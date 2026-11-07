import NNH_Tx2ConcreteInputs
open Aeneas Aeneas.Std
#print core.slice.index.SliceIndexRangeUsizeSlice
#print core.slice.index.SliceIndexRangeToUsizeSlice
#print UScalar.checked_add
#print AspisR1.Port4A_NativeReader.resume_source
open Lean in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  let s:=n.toString
  if (s.splitOn "Range").length>1 && ((s.splitOn "spec").length>1 || (s.splitOn "index").length>1 || (s.splitOn "get").length>1) && !(s.splitOn "_proof").length>1 then logInfo m!"{n}"
