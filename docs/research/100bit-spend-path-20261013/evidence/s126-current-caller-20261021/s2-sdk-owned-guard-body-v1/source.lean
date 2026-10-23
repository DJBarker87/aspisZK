import S2SdkOwnedGuardFrameV1
import S2SdkOwnedDecodedReuseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.GuardBody
open GuardRelease GuardAcquire GuardFrame

private def pairParts (value : Expr) : MetaM (Expr × Expr) := do
  let value ← instantiateMVars value
  unless value.getAppFn.isConstOf ``Prod.mk do throwError "Expected reached product constructor"
  let args := value.getAppArgs
  return (args[args.size-2]!,args.back!)

private def hasFact (type : Expr) : TacticM Bool := withMainContext do
  for decl in (← getLCtx) do
    if decl.type.getAppFn == type.getAppFn && (← isDefEq decl.type type) then return true
  return false

private def noneExpr : Expr := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Usize)

private def freshField (field : Expr) : TacticM Expr := withMainContext do
  if ← isDefEq field noneExpr then return ← mkEqRefl field
  let target ← mkEq field noneExpr
  for decl in (← getLCtx) do
    if decl.type.isAppOfArity ``Eq 3 && (← isDefEq decl.type target) then return mkFVar decl.fvarId
  throwError "Freshness not derived yet"

private def poseNew (proof : Expr) : TacticM Bool := withMainContext do
  if ← hasFact (← inferType proof) then return false
  let term ← Term.exprToSyntax proof
  let fact ← mkFreshUserName `liveGuard
  evalTactic (← `(tactic| have $(mkIdent fact) := $term))
  return true

/-- Install only postconditions of the actual reached acquisition calls.
Every generated proof term is checked by Lean; there is no SDK axiom. -/
elab "sdk_derive_guards" : tactic => withMainContext do
  let context := (← getLCtx)
  for decl in context do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let equation := decl.type.getAppArgs
    let lhs := equation[1]!
    let rhs := equation[2]!
    unless rhs.getAppFn.isConstOf ``Result.ok do continue
    let call := lhs.getAppArgs
    if lhs.getAppFn.isConstOf ``owned_acquire_checkpoint then
      let saved ← saveState
      try
        let (result,pair) ← pairParts rhs.getAppArgs.back!
        let (sdkOut,guardsOut) ← pairParts pair
        let wanted ← mkAppM ``LiveInvariant #[sdkOut,guardsOut]
        let np ← mkEq (mkProj ``LiveGuards 1 guardsOut) noneExpr
        let nq ← mkEq (mkProj ``LiveGuards 2 guardsOut) noneExpr
        if (← hasFact wanted) && (← hasFact np) && (← hasFact nq) then continue
        let proof ← mkAppM ``checkpoint_acquire_invariant
          #[call[0]!,sdkOut,call[2]!,result,guardsOut,mkFVar decl.fvarId]
        let term ← Term.exprToSyntax proof
        let inv ← mkFreshUserName `checkpointLive
        let pub ← mkFreshUserName `publicAbsent
        let prf ← mkFreshUserName `proofAbsent
        evalTactic (← `(tactic| obtain ⟨$(mkIdent inv),$(mkIdent pub),$(mkIdent prf)⟩ := $term))
        return
      catch _ => saved.restore
    if lhs.getAppFn.isConstOf ``owned_acquire_shared then
      let (result,sdkOut) ← pairParts rhs.getAppArgs.back!
      for inv in context do
        unless inv.type.getAppFn.isConstOf ``LiveInvariant do continue
        let args := inv.type.getAppArgs
        unless ← isDefEq args[0]! call[0]! do continue
        for mode in [false,true] do
          let saved ← saveState
          try
            let fresh ← freshField (mkProj ``LiveGuards (if mode then 2 else 1) args[1]!)
            let proof ← mkAppM ``shared_acquire_invariant
              #[call[0]!,sdkOut,args[1]!,call[1]!,mkConst (if mode then ``Bool.true else ``Bool.false),
                result,mkFVar inv.fvarId,fresh,mkFVar decl.fvarId]
            if ← poseNew proof then return
          catch _ => saved.restore
  throwError "No new reached acquisition invariant"

/-- The final checkpoint assignment uses the exact reached setter and old row. -/
elab "sdk_finish_guard_write" : tactic => withMainContext do
  let context := (← getLCtx)
  for inv in context do
    unless inv.type.getAppFn.isConstOf ``LiveInvariant do continue
    let args := inv.type.getAppArgs
    for decl in context do
      unless decl.type.isAppOfArity ``Eq 3 do continue
      let equation := decl.type.getAppArgs
      unless equation[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index_mut do continue
      unless equation[2]!.getAppFn.isConstOf ``Result.ok do continue
      let saved ← saveState
      try
        let call := equation[1]!.getAppArgs
        let (old,back) ← pairParts equation[2]!.getAppArgs.back!
        let bytes ← mkFreshExprMVar (← mkAppM ``alloc.vec.Vec #[mkConst ``U8])
        let proof ← mkAppM ``write_bytes_invariant
          #[args[0]!,args[1]!,call.back!,old,back,bytes,mkFVar inv.fvarId,mkFVar decl.fvarId]
        unless ← isDefEq (← inferType proof) (← getMainTarget) do throwError "Different write site"
        let term ← Term.exprToSyntax proof
        evalTactic (← `(tactic| exact $term))
        return
      catch _ => saved.restore
  throwError "No reached checkpoint assignment invariant"

/-- Every ordinary return of the complete emitted body establishes its own
release invariant, for both Ok and Err statuses and arbitrary child Ops.
This is a concrete parent theorem; no separate guard, slot or child success
is a premise. It does not assert total termination of the children/body. -/
theorem body_live_invariant (ops : SdkReference.Ops) (program : Array U8 32#usize)
    (sdk sdkOut : OwnedSdk) (data : Slice U8)
    (result : core.result.Result Unit solana_program_error.ProgramError) (guardsOut : LiveGuards)
    (h : owned_stage1_body ops program sdk data noGuards=ok (result,sdkOut,guardsOut)) :
    LiveInvariant sdkOut guardsOut := by
  have initial : LiveInvariant sdk noGuards := invariant_none sdk
  unfold owned_stage1_body at h
  repeat' first
    | assumption
    | sdk_constructor_evidence
    | sdk_derive_guards
    | solve | cases h; first | assumption | sdk_finish_guard_write
    | sdk_case_evidence
    | sdk_peel h
    | sdk_split h
    | sdk_reduce h
    | sdk_cases h
  all_goals
    have impossible : core.convert.Infallible := by assumption
    cases impossible

#print axioms body_live_invariant
end AspisS2OwnedStage1.SdkReference.GuardBody
