import NDO_JGn_ExactEval
set_option autoImplicit false
namespace AspisR1.JGn_PrefixEval
open Aeneas Aeneas.Std Result

theorem bind_continue {α β : Type} (x : Result α) (f : α → Result β) (a : α)
    (first : x=ok a) : (x >>= f)=f a := by rw [first,bind_tc_ok]
#print axioms bind_continue
end AspisR1.JGn_PrefixEval

open Lean Meta Elab Tactic
namespace AspisR1.JGn_PrefixEval
open JGn_ExactEval
partial def advance (stop : Nat) (input : Expr) : TacticM (Expr × Expr) := do
  let e ← withTransparency .all (whnfHeadPred input (fun t=>pure (!stops t)))
  let head := e.getAppFn.constName?.getD .anonymous
  let args := e.getAppArgs
  if loopHeads.contains head then
    let index := if head==``FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0 then args[2]! else args[args.size-1]!
    let idx ← mkAppM ``Aeneas.Std.UScalar.val #[index]
    let some n ← getNatValue? (← withTransparency .all (whnf idx)) | throwError "loop index not literal"
    if n==stop then
      let mut flat := #[]
      for a in args do flat := flat.push (← withTransparency .all (reduce a))
      let tail := mkAppN e.getAppFn flat
      return (tail,← mkEqRefl e)
  if head==``Bind.bind then
    let x := args[args.size-2]!
    let f := args[args.size-1]!
    let (a,ha) ← evaluate x
    let first ← withTransparency .all (mkAppM ``bind_continue #[x,f,a,ha])
    let (tail,next) ← advance stop (mkApp f a)
    return (tail,← withTransparency .all (mkEqTrans first next))
  let some eqns ← getEqnsFor? head | throwError "no prefix equation {head}: {e}"
  let mut rewritten : Option RewriteResult := none
  for eqn in eqns do
    if rewritten.isNone then
      try rewritten := some (← (← getMainGoal).rewrite e (← mkConstWithFreshMVarLevels eqn))
      catch _ => pure ()
  let some r := rewritten | throwError "prefix equation does not match {head}"
  let (tail,h) ← advance stop r.eNew
  pure (tail,← withTransparency .all (mkEqTrans r.eqProof h))

elab "jgn_tail " n:num source:term : tactic => do
  let e ← Term.elabTerm source none
  let (tail,_) ← advance n.getNat e
  let goal ← getMainGoal
  goal.assign tail
  replaceMainGoal []

elab "jgn_prefix " n:num : tactic => do
  let goal ← getMainGoal
  let some (_,lhs,rhs) := (← goal.getType).eq? | throwError "equality required"
  let (tail,h) ← advance n.getNat lhs
  unless ← withTransparency .all (isDefEq tail rhs) do throwError "prefix differs: {tail} versus {rhs}"
  withTransparency .all (goal.assign h)
  replaceMainGoal []
end AspisR1.JGn_PrefixEval
