import Aeneas
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  for n in [`Aeneas.Std.core.fmt.Formatter, `Aeneas.Std.core.fmt.Error, `Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt, `core.fmt.Formatter] do
    match env.find? n with
    | none => logInfo m!"PV_FA_MISSING {n}"
    | some ci =>
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "def"
        | .opaqueInfo _ => "opaque"
        | .thmInfo _ => "theorem"
        | _ => "other"
      let mod := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
      logInfo m!"PV_FA_DECL {n} {kind} {mod}"
#print Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt
