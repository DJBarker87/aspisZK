import PV_B3P_ClosureLinks14227
open Lean Elab Command
run_cmd do
 let environment ← getEnv
 for (name, info) in environment.constants.toList do
  let s := name.toString
  if (s.startsWith "Aeneas.Std.core.array" || s.startsWith "Aeneas.Std.Array" ||
      s.startsWith "Aeneas.Std.core.iter.adapters.step_by") &&
      (s.endsWith "from_fn" || s.endsWith "map" || s.endsWith "next" || s.endsWith "new" || s.endsWith "fold") then
   logInfo m!"{name} : {info.type}"
#print Aeneas.Std.core.iter.traits.iterator.Iterator.step_by.default
#print Aeneas.Std.Slice.subslice
#print Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index
