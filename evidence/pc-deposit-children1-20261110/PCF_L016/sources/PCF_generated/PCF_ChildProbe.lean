import NFY_Part053
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for s in ["AspisR1.S2K.DigestBytes.bytes", "AspisR1.S2K.DigestBytes.word",
      "AspisR1.S2K.DigestBytes.wordBytes", "AspisR1.S2K.DigestBytes.byte",
      "AspisR1.S2K.DigestBytes.exact", "NFY_NBP_DigestEncode.result",
      "Aeneas.Std.Slice.setSlice!", "Aeneas.Std.core.slice.iter.Iter.mk",
      "Aeneas.Std.core.iter.adapters.enumerate.Enumerate.mk"] do
    match env.find? s.toName with
    | none => logInfo m!"MISSING {s}"
    | some ci => logInfo m!"FOUND {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
