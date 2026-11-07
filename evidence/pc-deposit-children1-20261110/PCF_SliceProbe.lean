import Aeneas
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.splitOn "setSlice").length > 1 || s == "Aeneas.Std.core.slice.iter.IteratorSliceIter.next" ||
       s == "Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut" ||
       s == "Aeneas.Std.core.slice.Slice.copy_from_slice" then
      logInfo m!"FOUND {s}\nTYPE {ci.type}"
      if s == "Aeneas.Std.core.slice.iter.IteratorSliceIter.next" ||
         s == "List.setSlice!" || s == "Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut" ||
         s == "Aeneas.Std.core.slice.Slice.copy_from_slice" then
        logInfo m!"VALUE {ci.value? true}"
