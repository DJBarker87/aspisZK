import JGn_FieldExact
set_option autoImplicit false
open Lean Meta Elab Tactic
namespace AspisR1.JGn_ExactEval

def fieldHeads : List Name := [``FIq_Native.field.QM31.add,``FIq_Native.field.QM31.sub,``FIq_Native.field.QM31.mul]
def stops (e : Expr) : Bool :=
  fieldHeads.contains e.getAppFn.constName! ||
  [``Bind.bind,``Aeneas.Std.Result.ok,``Aeneas.Std.Result.fail,``Aeneas.Std.Result.div].contains e.getAppFn.constName!

def parseTerm (s : String) : TacticM Expr := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term s with
    | .ok stx => pure stx
    | .error err => throwError "{err}"
  Term.elabTerm stx none

def literal (w : JGl_WordProof.Words) : TacticM Expr :=
  parseTerm s!"(⟨⟨{w.1.1}#u32,{w.1.2}#u32⟩,⟨{w.2.1}#u32,{w.2.2}#u32⟩⟩ : FIq_Native.field.QM31)"

def canon (x : Expr) : TacticM Expr := do
  let t ← mkAppM ``FIv_NativeValue.Canon #[x]
  let m ← mkFreshExprSyntheticOpaqueMVar t
  let gs ← getGoals
  setGoals [m.mvarId!]
  evalTactic (← `(tactic| norm_num [FIv_NativeValue.Canon,
    FIv_NativeArithmetic.qm,FIv_NativeArithmetic.cm,
    ExtractedMaskQM31Exact.CurrentCanonicalQM,
    ExtractedMaskTowerAdd.CanonicalQM,ExtractedMaskTowerAdd.CanonicalCM,ExtractedMaskTowerAdd.P]))
  unless (← getGoals).isEmpty do throwError "canonical literal certificate failed {x}"
  setGoals gs
  instantiateMVars m

def field (e : Expr) : TacticM (Expr × Expr) := do
  let args := e.getAppArgs
  let x := args[args.size-2]!
  let y := args[args.size-1]!
  let dx ← mkAppM ``FIv_NativeValue.decode #[x]
  let dy ← mkAppM ``FIv_NativeValue.decode #[y]
  let name := e.getAppFn.constName!
  let op := if name==``FIq_Native.field.QM31.add then ``HAdd.hAdd else if name==``FIq_Native.field.QM31.sub then ``HSub.hSub else ``HMul.hMul
  let math ← mkAppM op #[dx,dy]
  let cache ← IO.mkRef ({} : Std.HashMap Expr (JGl_WordProof.Words × Expr))
  let (w,hv) ← JGl_WordProof.reflect cache math
  let z ← literal w
  let thm := if name==``FIq_Native.field.QM31.add then ``JGn_FieldExact.add else if name==``FIq_Native.field.QM31.sub then ``JGn_FieldExact.sub else ``JGn_FieldExact.mul
  let h ← mkAppM thm #[x,y,z,← canon x,← canon y,← canon z,hv]
  pure (z,h)

partial def evaluate (input : Expr) : TacticM (Expr × Expr) := do
  let e ← whnfHeadPred input (fun t=>pure (!stops t))
  let head := e.getAppFn.constName!
  let args := e.getAppArgs
  if fieldHeads.contains head then field e
  else if head==``Aeneas.Std.Result.ok then
    pure (args[args.size-1]!,← mkEqRefl e)
  else if head==``Bind.bind then
    let x := args[args.size-2]!
    let f := args[args.size-1]!
    let (a,ha) ← evaluate x
    let (b,hb) ← evaluate (mkApp f a)
    pure (b,← mkAppM ``JGn_FieldExact.bind #[x,f,a,b,ha,hb])
  else
    let some eqns ← getEqnsFor? head | throwError "no reduction/equations for {head}: {e}"
    let mut result : Option (Expr × Expr) := none
    for eqn in eqns do
      if result.isNone then
        try
          let r ← rewrite e (← mkConstWithFreshMVarLevels eqn)
          let (out,tail) ← evaluate r.eNew
          result := some (out,← mkEqTrans r.eqProof tail)
        catch _ => pure ()
    match result with
    | some r => pure r
    | none => throwError "no successful equation for {head}"

elab "jgn_eval" : tactic => do
  let goal ← getMainGoal
  let some (_,lhs,rhs) := (← goal.getType).eq? | throwError "equality required"
  let (_,h) ← evaluate lhs
  let some (_,_,actual) := (← inferType h).eq? | throwError "bad result"
  unless ← isDefEq actual rhs do throwError "actual return {actual}, requested {rhs}"
  goal.assign h
  replaceMainGoal []
end AspisR1.JGn_ExactEval
