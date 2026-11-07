import Aeneas
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for s in ["Aeneas.Std.UScalar.cast", "Aeneas.Std.UScalar.and",
      "Aeneas.Std.UScalar.cast_val_eq", "Aeneas.Std.UScalar.val_cast",
      "Aeneas.Std.UScalar.land_val", "Aeneas.Std.UScalar.and_val",
      "Aeneas.Std.Scalar.eq_iff", "Nat.and_two_pow_sub_one_eq_mod",
      "Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate.next",
      "Aeneas.Std.core.slice.iter.Iter", "Aeneas.Std.core.iter.adapters.enumerate.Enumerate"] do
    match env.find? s.toName with
    | none => logInfo m!"MISSING {s}"
    | some ci => logInfo m!"FOUND {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
