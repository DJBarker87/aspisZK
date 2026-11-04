import NGD_DecodeEntry
import NGD_ParseReference
open Aeneas Aeneas.Std Result
#print List.toChunksExact
#print AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop
#print AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop.body
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  if n.toString.startsWith "List.toChunksExact" ||
      n.toString.startsWith "Aeneas.Std.Array.set_" then
   Lean.logInfo m!"{n}: {ci.type}"
