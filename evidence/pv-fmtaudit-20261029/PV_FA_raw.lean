import Aeneas
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  for root in [`Aeneas.Std.core.fmt.Formatter, `Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt] do
    let mut todo := [root]
    let mut seen : NameSet := {}
    let mut axs : NameSet := {}
    let mut missing : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      match env.checked.get.find? n with
      | none => missing := missing.insert n
      | some ci =>
        if ci matches .axiomInfo _ then axs := axs.insert n
        todo := ci.type.getUsedConstants.toList ++ (ci.value?.map Expr.getUsedConstants |>.getD #[]).toList ++ todo
    logInfo m!"PV_FA_RAW {root} axioms={axs.toArray} missing={missing.toArray} visited={seen.size}"
