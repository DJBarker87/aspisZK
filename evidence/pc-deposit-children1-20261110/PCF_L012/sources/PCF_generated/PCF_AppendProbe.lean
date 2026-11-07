import Aeneas
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for s in ["Aeneas.Std.core.slice.iter.Iter.mk", "Aeneas.Std.core.iter.adapters.enumerate.Enumerate.mk",
      "Aeneas.Std.core.iter.traits.iterator.IteratorSliceIter",
      "Aeneas.Std.core.slice.Slice.iter", "Aeneas.Std.core.slice.iter.Iter.next",
      "Aeneas.Std.Slice.getElem?_eq_getElem", "Aeneas.Std.UScalar.eq_iff",
      "Aeneas.Std.UScalar.val_inj", "Aeneas.Std.UScalar.eq_of_val_eq"] do
    match env.find? s.toName with
    | none => logInfo m!"MISSING {s}"
    | some ci => logInfo m!"FOUND {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
