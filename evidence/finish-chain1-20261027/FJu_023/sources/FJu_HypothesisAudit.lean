import FJu_Top
import FJu_EndpointIdentity
import Lean
open Lean Meta Elab
run_meta do
  for (name,predicate) in [
      (``AspisR1.FJp_Finish.Outcome,``AspisR1.R3SemanticRemainingJoins.EquationEndpoint),
      (``AspisR1.FJu_Finish.Outcome,``AspisR1.FJu_Remaining.Endpoint)] do
    let info ← getConstInfo name
    let some body := info.value? true | throwError "Missing native outcome body"
    let seen ← IO.mkRef (0 : Nat)
    body.forEach fun e => do
      match e with
      | .forallE n domain _ _ =>
        if n == `semantic_S3_S9 then
          unless domain.getAppFn.isConstOf predicate do
            throwError "Unexpected semantic binder domain in {name}"
          seen.modify (· + 1)
      | _ => pure ()
    let count ← seen.get
    unless count == 1 do throwError "Expected exactly one semantic HYPOTHESIS in {name}, got {count}"
    logInfo m!"NATIVE HYPOTHESIS: {name}.semantic_S3_S9 has exactly the selected endpoint domain"
  for (name,predicate) in [
      (``AspisR1.FJp_Top.deployed,``AspisR1.FJp_GlobalOwners.Owners),
      (``AspisR1.FJu_Top.deployed,``AspisR1.FJu_GlobalOwners.Owners)] do
    let info ← getConstInfo name
    let seen ← IO.mkRef (0 : Nat)
    info.type.forEach fun e => do
      match e with
      | .forallE n domain _ _ =>
        if n == `finishOwners then
          unless domain.getAppFn.isConstOf predicate do
            throwError "Unexpected owner binder domain in {name}"
          seen.modify (· + 1)
      | _ => pure ()
    let count ← seen.get
    unless count == 1 do throwError "Expected exactly one global HYPOTHESIS in {name}, got {count}"
    logInfo m!"GLOBAL HYPOTHESIS: {name}.finishOwners has exactly the selected owner domain"
#print axioms AspisR1.FJu_Top.deployed
#print axioms AspisR1.FJu_EndpointIdentity.residual
