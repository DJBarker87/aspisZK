import NIT_LowInterpretation
open Aeneas Aeneas.Std
#print core.num.U32.from_le_bytes
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for entry in env.constants.toList do
  let s := entry.1.toString
  if ((s.splitOn "from_le_bytes").length>1) &&
    (s.startsWith "Aeneas.Std." || (s.splitOn "U32").length>1) then
   logInfo m!"{entry.1}"
#print BitVec.fromLEBytes
run_cmd do
 let env ← getEnv
 for entry in env.constants.toList do
  let s := entry.1.toString
  if (s.splitOn "fromLEBytes").length>1 then logInfo m!"{entry.1}"
