import PV_L1E_SafeObserve
import Lean
open Lean Elab Tactic Meta

/-- Select only the syntactically named logged callee. Do not delta-reduce
unrelated large source programs while trying a list of candidate lemmas. -/
elab "l1e_safe_callee" : tactic => do
  let t ← getMainTarget
  let args := t.getAppArgs
  if args.isEmpty then throwError "not a Safe application"
  let some name := args.back!.getAppFn.constName? | throwError "not a named callee"
  let s := name.toString
  unless s.endsWith ".produce" do throwError "not a logged producer"
  let m := s.dropEnd 8 |>.toString
  let lemma := Name.str (Name.mkSimple "PV_L1E_CallbackSafety") ("safe_" ++ m)
  evalTactic (← `(tactic| apply $(mkIdent lemma)))

/-- Only an actual observe node may invoke the phase-entry theorem. -/
elab "l1e_safe_observe" : tactic => do
  let t ← getMainTarget
  let args := t.getAppArgs
  if args.isEmpty then throwError "not a Safe application"
  unless args.back!.getAppFn.constName? == some ``PV_L1D_Logged.observe do
    throwError "not an observation"
  evalTactic (← `(tactic| exact PV_L1E_SafeObserve.phase _ _ _ (by intro h; cases h)))
