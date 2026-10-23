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

private def sameInvariant (left right : Expr) : MetaM Bool := do
  unless left.getAppFn.isConstOf ``LiveInvariant && right.getAppFn.isConstOf ``LiveInvariant do return false
  let la := left.getAppArgs
  let ra := right.getAppArgs
  unless ← withTransparency .reducible <| isDefEq la[0]! ra[0]! do return false
  let lg ← whnf la[1]!
  let rg ← whnf ra[1]!
  withTransparency .default <| isDefEq lg rg

private def hasFact (type : Expr) : TacticM Bool := withMainContext do
  for decl in (← getLCtx) do
    if type.getAppFn.isConstOf ``LiveInvariant then
      if ← sameInvariant decl.type type then return true
    else if decl.type.getAppFn == type.getAppFn &&
      (← withTransparency .reducible <| isDefEq decl.type type) then return true
  return false

elab "sdk_guard_assumption" : tactic => withMainContext do
  let target ← getMainTarget
  for decl in (← getLCtx) do
    if ← sameInvariant decl.type target then
      let term ← Term.exprToSyntax (mkFVar decl.fvarId)
      evalTactic (← `(tactic| exact $term))
      return
  throwError "No matching reached live-guard fact"

private def noneExpr : Expr := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Usize)

private def freshField (field : Expr) : TacticM Expr := withMainContext do
  let field ← whnf field
  if ← withTransparency .reducible <| isDefEq field noneExpr then return ← mkEqRefl field
  let target ← mkEq field noneExpr
  for decl in (← getLCtx) do
    if decl.type.isAppOfArity ``Eq 3 && (← withTransparency .reducible <| isDefEq decl.type target) then return mkFVar decl.fvarId
  throwError "Freshness not derived yet"

private def poseNew (proof : Expr) : TacticM Bool := withMainContext do
  if ← hasFact (← inferType proof) then return false
  let fact ← mkFreshUserName `liveGuard
  let next ← (← getMainGoal).assert fact (← inferType proof) proof
  let (_, next) ← next.intro1
  replaceMainGoal [next]
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
        unless ← withTransparency .reducible <| isDefEq args[0]! call[0]! do continue
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
  let target ← getMainTarget
  unless target.getAppFn.isConstOf ``LiveInvariant do throwError "Not a live-guard goal"
  unless target.getAppArgs[0]!.getAppFn.isConstOf ``OwnedSdk.mk do throwError "Not the final SDK record update"
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

private def rewriteOuter (h : TSyntax `ident) (lhs rhs : Expr) : TacticM Unit := do
  let type ← mkEq lhs rhs
  let term ← Term.exprToSyntax type
  evalTactic (← `(tactic| change $term at $h:ident))

/-- Cases only the status supplied to a reached standard Try operation,
without unfolding later parent branches or arbitrary child implementations. -/
elab "sdk_guard_status" : tactic => withMainContext do
  for decl in (← getLCtx) do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let lhs := decl.type.getAppArgs[1]!
    unless lhs.getAppFn.isConstOf ``core.result.Result.Insts.CoreOpsTry.branch ||
      lhs.getAppFn.isConstOf ``core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual do continue
    let operand := lhs.getAppArgs.back!
    if operand.isFVar then
      let source ← operand.fvarId!.getDecl
      evalTactic (← `(tactic| cases $(mkIdent source.userName):ident))
      return
    let reduced ← whnf lhs
    if reduced.getAppFn.isConstOf ``Result.ok then
      evalTactic (← `(tactic| cases $(mkIdent decl.userName):ident))
      return
  throwError "No unresolved reached Try status"

private theorem terminal_invariant
    (leftResult rightResult : core.result.Result Unit solana_program_error.ProgramError)
    (leftSdk rightSdk : OwnedSdk) (leftGuards rightGuards : LiveGuards)
    (h : Result.ok (leftResult,leftSdk,leftGuards)=Result.ok (rightResult,rightSdk,rightGuards))
    (held : LiveInvariant leftSdk leftGuards) : LiveInvariant rightSdk rightGuards := by
  cases h
  exact held

/-- One outer control step only. Never try dependent cases on a large bind,
and never ask simplification to traverse the entire emitted parent body. -/
elab "sdk_guard_step " h:ident : tactic => withMainContext do
  let decl ← (← getFVarId h).getDecl
  let args := decl.type.getAppArgs
  let lhs := args[1]!.consumeMData
  let rhs := args[2]!
  if let .letE _ _ value body _ := lhs then
    rewriteOuter h (body.instantiate1 value) rhs
    return
  if lhs.getAppFn.isConstOf ``Aeneas.Std.uncurry then
    evalTactic (← `(tactic| simp only [Aeneas.Std.uncurry] at $h:ident))
    return
  if lhs.getAppFn.isConstOf ``Result.ok then
    let (leftResult,leftPair) ← pairParts lhs.getAppArgs.back!
    let (leftSdk,leftGuards) ← pairParts leftPair
    let (rightResult,rightPair) ← pairParts rhs.getAppArgs.back!
    let (rightSdk,rightGuards) ← pairParts rightPair
    let needed ← mkFreshExprMVar (← mkAppM ``LiveInvariant #[leftSdk,leftGuards])
    let proof ← mkAppM ``terminal_invariant
      #[leftResult,rightResult,leftSdk,rightSdk,leftGuards,rightGuards,mkFVar decl.fvarId,needed]
    unless ← withTransparency .reducible <| isDefEq (← inferType proof) (← getMainTarget) do
      throwError "Different terminal output"
    (← getMainGoal).assign proof
    replaceMainGoal [needed.mvarId!]
    evalTactic (← `(tactic| first | sdk_guard_assumption | sdk_finish_guard_write))
    return
  if lhs.getAppFn.isConstOf ``Result.fail || lhs.getAppFn.isConstOf ``Result.div then
    evalTactic (← `(tactic| cases $h:ident))
    return
  if lhs.getAppFn.isConstOf ``ite then
    evalTactic (← `(tactic| sdk_split $h:ident))
    return
  if lhs.getAppFn.isConstOf ``Bind.bind then
    evalTactic (← `(tactic| sdk_peel $h:ident))
    return
  if let some reduced ← reduceRecMatcher? lhs then
    rewriteOuter h reduced rhs
    return
  if let some matched ← matchMatcherApp? lhs true then
    for discriminant in matched.discrs do
      if discriminant.isFVar then
        let source ← discriminant.fvarId!.getDecl
        evalTactic (← `(tactic| cases $(mkIdent source.userName):ident))
        return
  throwError "No supported outer step, head {lhs.getAppFn}"

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
    | sdk_guard_assumption
    | sdk_derive_guards
    | sdk_guard_status
    | sdk_guard_step h
  all_goals
    have impossible : core.convert.Infallible := by assumption
    cases impossible

/-- Once the concrete body returns an ordinary SDK status, its exact finalizer
terminates and preserves that status. Neither a release-success premise nor a
separately assumed live-guard invariant is required. This is conditional on a
body return, not a totality claim for arbitrary external child operations. -/
theorem body_return_finalizes (ops : SdkReference.Ops) (program : Array U8 32#usize)
    (sdk sdkBody : OwnedSdk) (data : alloc.vec.Vec U8)
    (status : core.result.Result Unit solana_program_error.ProgramError) (guards : LiveGuards)
    (body : owned_stage1_body ops program sdk (alloc.vec.Vec.deref data) noGuards =
      ok (status,sdkBody,guards)) :
    ∃ sdkOut, owned_stage1 ops program sdk data=ok (status,sdkOut) := by
  have held := body_live_invariant ops program sdk sdkBody (alloc.vec.Vec.deref data)
    status guards body
  obtain ⟨sdkOut,released⟩ := release_total sdkBody guards held
  refine ⟨sdkOut,?_⟩
  simp only [owned_stage1,body,bind_tc_ok,released]

#print axioms body_live_invariant
#print axioms body_return_finalizes
end AspisS2OwnedStage1.SdkReference.GuardBody
