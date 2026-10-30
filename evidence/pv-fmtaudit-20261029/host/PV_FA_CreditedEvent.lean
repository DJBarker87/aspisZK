import R1Z.PV_FXM_DropSelected
import R1Z.PV_FXM_ReserveSelected
import PV_B3P_Install132
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  for root in [`R1Z.PV_FXM_DropSelected.execution, `R1Z.PV_FXM_ReserveSelected.complete, `PV_B3P_Install132.reference] do
    let mut todo := [root]
    let mut seen : NameSet := {}
    let mut axs : NameSet := {}
    let mut missing : NameSet := {}
    let mut fmts : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if (toString n).startsWith "Aeneas.Std.core.fmt" then fmts := fmts.insert n
      match env.checked.get.find? n with
      | none => missing := missing.insert n
      | some ci =>
        if ci matches .axiomInfo _ then axs := axs.insert n
        todo := ci.type.getUsedConstants.toList ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]).toList ++ todo
    logInfo m!"PV_FA_CONE {root} axioms={axs.toArray} fmt={fmts.toArray} missing={missing.toArray} visited={seen.size}"
#print axioms R1Z.PV_FXM_DropSelected.execution
#print axioms R1Z.PV_FXM_ReserveSelected.complete
#print axioms PV_B3P_Install132.reference
