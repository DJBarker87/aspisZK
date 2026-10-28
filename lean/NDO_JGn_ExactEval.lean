import NDO_JGn_FieldExact
import NDO_JGi_PrepareForward
set_option autoImplicit false
open Lean Meta Elab Tactic
namespace AspisR1.JGn_ExactEval

def fieldHeads : List Name := [``FIq_Native.field.QM31.add,``FIq_Native.field.QM31.sub,``FIq_Native.field.QM31.mul]
def loopHeads : List Name := [
  ``FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0,
  ``FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1,
  ``FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0,
  ``FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop,
  ``FIq_Native.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop,
  ``FIq_Native.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop]
def stops (e : Expr) : Bool :=
  loopHeads.contains (e.getAppFn.constName?.getD .anonymous) ||
  fieldHeads.contains (e.getAppFn.constName?.getD .anonymous) ||
  [``HAdd.hAdd,``Bind.bind,``Aeneas.Std.Result.ok,``Aeneas.Std.Result.fail,``Aeneas.Std.Result.div].contains (e.getAppFn.constName?.getD .anonymous)

def parseTerm (s : String) : TacticM Expr := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term s with
    | .ok stx => pure stx
    | .error err => throwError "{err}"
  Term.elabTerm stx none

def literal (w : JGl_WordProof.Words) : TacticM Expr :=
  parseTerm s!"(⟨⟨{w.1.1}#u32,{w.1.2}#u32⟩,⟨{w.2.1}#u32,{w.2.2}#u32⟩⟩ : FIq_Native.field.QM31)"

def canon (x : Expr) : TacticM Expr := do
  let mut ns : Array Nat := #[]
  for component in [``FIq_Native.field.QM31.c0,``FIq_Native.field.QM31.c1] do
    let c ← mkAppM component #[x]
    for lane in [``FIq_Native.field.CM31.a,``FIq_Native.field.CM31.b] do
      let w ← mkAppM lane #[c]
      let v ← mkAppM ``Aeneas.Std.UScalar.val #[w]
      let some n ← getNatValue? (← withTransparency .all (whnf v)) | throwError "nonliteral canonical lane"
      ns := ns.push n
  let t ← parseTerm s!"((({ns[0]!} : Nat) < 2147483647 ∧ ({ns[1]!} : Nat) < 2147483647) ∧ (({ns[2]!} : Nat) < 2147483647 ∧ ({ns[3]!} : Nat) < 2147483647))"
  let m ← mkFreshExprSyntheticOpaqueMVar t
  let gs ← getGoals
  setGoals [m.mvarId!]
  evalTactic (← `(tactic| norm_num))
  unless (← getGoals).isEmpty do throwError "canonical literal certificate failed {x}"
  setGoals gs
  instantiateMVars m

def field (e : Expr) : TacticM (Expr × Expr) := do
  let args := e.getAppArgs
  let x ← withTransparency .all (reduce args[args.size-2]!)
  let y ← withTransparency .all (reduce args[args.size-1]!)
  let dx ← mkAppM ``FIv_NativeValue.decode #[x]
  let dy ← mkAppM ``FIv_NativeValue.decode #[y]
  let opName := (e.getAppFn.constName?.getD .anonymous)
  let op := if opName==``FIq_Native.field.QM31.add then ``HAdd.hAdd else if opName==``FIq_Native.field.QM31.sub then ``HSub.hSub else ``HMul.hMul
  let math ← mkAppM op #[dx,dy]
  let cache ← IO.mkRef ({} : Std.HashMap Expr (JGl_WordProof.Words × Expr))
  let (w,hv) ← JGl_WordProof.reflect cache math
  let z ← literal w
  let thm := if opName==``FIq_Native.field.QM31.add then ``JGn_FieldExact.add else if opName==``FIq_Native.field.QM31.sub then ``JGn_FieldExact.sub else ``JGn_FieldExact.mul
  let h ← mkAppM thm #[x,y,z,← canon x,← canon y,← canon z,hv]
  pure (z,h)

def scalarAdd (e : Expr) : TacticM (Expr × Expr) := do
  let args := e.getAppArgs
  let x := args[args.size-2]!
  let y := args[args.size-1]!
  let xt ← withTransparency .all (whnf (← inferType x))
  let ty := xt.getAppArgs[0]!
  let kind := ty.getAppFn.constName?.getD .anonymous
  let suffix := if kind==``Aeneas.Std.UScalarTy.Usize then "usize"
    else if kind==``Aeneas.Std.UScalarTy.U64 then "u64"
    else if kind==``Aeneas.Std.UScalarTy.U32 then "u32"
    else if kind==``Aeneas.Std.UScalarTy.U16 then "u16" else "u8"
  let vx ← mkAppM ``Aeneas.Std.UScalar.val #[x]
  let vy ← mkAppM ``Aeneas.Std.UScalar.val #[y]
  let some nx ← getNatValue? (← withTransparency .all (whnf vx)) | throwError "nonliteral scalar add left"
  let some ny ← getNatValue? (← withTransparency .all (whnf vy)) | throwError "nonliteral scalar add right"
  let z ← parseTerm s!"({nx+ny}#{suffix})"
  let h ← mkAppM ``JGi_PrepareForward.checked_add #[x,y,z,← mkEqRefl (mkNatLit (nx+ny))]
  pure (z,h)

partial def evaluate (input : Expr) : TacticM (Expr × Expr) := do
  let e ← withTransparency .all (whnfHeadPred input (fun t=>pure (!stops t)))
  let head := (e.getAppFn.constName?.getD .anonymous)
  let args := e.getAppArgs
  if fieldHeads.contains head then field e
  else if head==``HAdd.hAdd then scalarAdd e
  else if head==``Aeneas.Std.Result.ok then
    pure (args[args.size-1]!,← mkEqRefl e)
  else if head==``Bind.bind then
    let x := args[args.size-2]!
    let f := args[args.size-1]!
    let (a,ha) ← evaluate x
    let (b,hb) ← evaluate (mkApp f a)
    pure (b,← withTransparency .all (mkAppM ``JGn_FieldExact.bind #[x,f,a,b,ha,hb]))
  else if (head.toString.splitOn "ofOption.match").length>1 then
    let reduced ← withTransparency .all (reduce e)
    if reduced==e then throwError "scalar Option reduction stuck {e}"
    let (out,h) ← evaluate reduced
    pure (out,h)
  else
    let some eqns ← getEqnsFor? head | throwError "no reduction/equations for {head}: {e}"
    let mut result : Option RewriteResult := none
    for eqn in eqns do
      if result.isNone then
        try result := some (← (← getMainGoal).rewrite e (← mkConstWithFreshMVarLevels eqn))
        catch _ => pure ()
    match result with
    | some r =>
      let (out,tail) ← evaluate r.eNew
      pure (out,← withTransparency .all (mkEqTrans r.eqProof tail))
    | none => throwError "no matching equation for {head}"

elab "jgn_eval" : tactic => do
  let goal ← getMainGoal
  let some (_,lhs,rhs) := (← goal.getType).eq? | throwError "equality required"
  let (_,h) ← evaluate lhs
  let some (_,_,actual) := (← inferType h).eq? | throwError "bad result"
  unless ← withTransparency .all (isDefEq actual rhs) do throwError "actual return {actual}, requested {rhs}"
  withTransparency .all (goal.assign h)
  replaceMainGoal []
end AspisR1.JGn_ExactEval

open Lean Meta Elab Tactic in
elab "jgn_return " source:term : tactic => do
  let e ← Term.elabTerm source none
  let (out,_) ← AspisR1.JGn_ExactEval.evaluate e
  let goal ← getMainGoal
  goal.assign out
  replaceMainGoal []
