import Aeneas
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for s in ["Aeneas.Std.core.slice.iter.Iter",
      "Aeneas.Std.core.iter.adapters.enumerate.Enumerate",
      "Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate.next",
      "Aeneas.Std.core.iter.traits.iterator.IteratorSliceIter",
      "Aeneas.Std.core.slice.Slice.iter",
      "Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut",
      "Aeneas.Std.core.slice.Slice.copy_from_slice",
      "Aeneas.Std.Slice.setSlice!", "List.length_setSlice!"] do
    let n := s.toName
    match env.find? n with
    | none => logInfo m!"MISSING {s}"
    | some ci => logInfo m!"FOUND {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
