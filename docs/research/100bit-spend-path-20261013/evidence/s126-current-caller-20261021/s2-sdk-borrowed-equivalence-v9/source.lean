import S2SdkBorrowedBufferFrameV1
import S2SdkBorrowedScanV1
import S2SdkSnapshotEquivalenceV1
import S2SdkOwnedGuardBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.BorrowedEquivalence

private theorem bind_congr_reached {A B : Type} (m : Result A)
    (f g : A → Result B) (same : ∀ a,m=ok a → f a=g a) :
    (do let a ← m; f a)=(do let a ← m; g a) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok a => exact same a rfl

private theorem acquired_read (sdk out : OwnedSdk) (acquired queried : Usize)
    (result : core.result.Result Unit solana_program_error.ProgramError)
    (prior : OwnedDataCell)
    (execution : BorrowedReference.owned_acquire_shared sdk acquired=ok (result,out))
    (reached : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells queried=ok prior) :
    ∃ cell, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      out.data_cells queried=ok cell ∧ cell.bytes=prior.bytes := by
  have same := BorrowedBufferFrame.acquire_preserves_read sdk out acquired queried result execution
  have before : BorrowedBufferFrame.readBytes sdk queried=ok prior.bytes := by
    simp only [BorrowedBufferFrame.readBytes,reached,bind_tc_ok]
  have after := same.trans before
  unfold BorrowedBufferFrame.readBytes at after
  cases read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      out.data_cells queried with
  | fail error => simp only [read,bind_tc_fail] at after; cases after
  | div => simp only [read,bind_tc_div] at after; cases after
  | ok cell =>
    simp only [read,bind_tc_ok] at after
    exact ⟨cell,rfl,Result.ok.inj after⟩

private partial def unpack (n : Name) : TacticM Unit := withMainContext do
  let d ← getLocalDeclFromUserName n
  if (← whnf d.type).getAppFn.isConstOf ``Prod then
    let a ← mkFreshUserName `part
    let b ← mkFreshUserName `part
    evalTactic (← `(tactic| rcases $(mkIdent n):ident with ⟨$(mkIdent a),$(mkIdent b)⟩))
    unpack a
    unpack b

elab "borrowed_step" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOfArity ``Eq 3 do throwError "Expected equality"
  let args := target.getAppArgs
  let left := args[1]!.consumeMData
  let right := args[2]!.consumeMData
  logInfo m!"outer: {left.getAppFn} / {right.getAppFn}"
  let l := match left with | .letE _ _ v b _ => b.instantiate1 v | _ => left
  let r := match right with | .letE _ _ v b _ => b.instantiate1 v | _ => right
  if l != left || r != right then
    let t ← Term.exprToSyntax (← mkEq l r)
    evalTactic (← `(tactic| change $t))
    return
  if left.getAppFn.isConstOf ``Bind.bind && right.getAppFn.isConstOf ``Bind.bind then
    let la := left.getAppArgs
    let ra := right.getAppArgs
    let lm := la[la.size-2]!
    let rm := ra[ra.size-2]!
    unless ← withTransparency .all <| isDefEq lm rm do
      throwError "Different reached operations: {lm} / {rm}"
    let applied ← mkAppM ``bind_congr_reached #[lm,la.back!,ra.back!]
    let appliedType ← whnf (← inferType applied)
    unless appliedType.isForall do throwError "Expected reached continuation premise"
    let premise ← mkFreshExprMVar appliedType.bindingDomain!
    let proof := mkApp applied premise
    unless ← withTransparency .all <| isDefEq (← inferType proof) target do
      throwError "Different bind structure"
    (← getMainGoal).assign proof
    replaceMainGoal [premise.mvarId!]
    let value ← mkFreshUserName `value
    let reached ← mkFreshUserName `reached
    evalTactic (← `(tactic| intro $(mkIdent value) $(mkIdent reached)))
    unpack value
    return
  if left.getAppFn.isConstOf ``ite then
    let condition ← Term.exprToSyntax left.getAppArgs[1]!
    let branch ← mkFreshUserName `branch
    evalTactic (← `(tactic| by_cases $(mkIdent branch) : $condition))
    evalTactic (← `(tactic| all_goals first
      | simp only [if_pos $(mkIdent branch)]
      | simp only [if_neg $(mkIdent branch)]))
    return
  if let some matched ← matchMatcherApp? left true then
    for discriminant in matched.discrs do
      if discriminant.isFVar then
        let d ← discriminant.fvarId!.getDecl
        evalTactic (← `(tactic| cases $(mkIdent d.userName):ident))
        return
  if let some reduced ← reduceRecMatcher? left then
    let t ← Term.exprToSyntax (← mkEq reduced right)
    evalTactic (← `(tactic| change $t))
    return
  if let some reduced ← reduceRecMatcher? right then
    let t ← Term.exprToSyntax (← mkEq left reduced)
    evalTactic (← `(tactic| change $t))
    return
  if left.getAppFn.isConstOf ``Result.ok || left.getAppFn.isConstOf ``Result.fail ||
      left.getAppFn.isConstOf ``Result.div then
    if ← withTransparency .all <| isDefEq left right then
      (← getMainGoal).assign (← mkEqRefl left)
      replaceMainGoal []
      return
  throwError "Unsupported outer equality: {left.getAppFn} / {right.getAppFn}"

elab "borrowed_frame" : tactic => withMainContext do
  let target ← getMainTarget
  let left := target.getAppArgs[1]!
  unless left.getAppFn.isConstOf ``Bind.bind do throwError "Not a reached bind"
  let la := left.getAppArgs
  let operation := la[la.size-2]!
  unless operation.getAppFn.isConstOf ``alloc.vec.Vec.index do throwError "Not a cell read"
  let readArgs := operation.getAppArgs
  let context ← getLCtx
  for acquired in context do
    unless acquired.type.isAppOfArity ``Eq 3 do continue
    let aa := acquired.type.getAppArgs
    unless aa[1]!.getAppFn.isConstOf ``BorrowedReference.owned_acquire_shared do continue
    unless aa[2]!.getAppFn.isConstOf ``Result.ok do continue
    let call := aa[1]!.getAppArgs
    let pair := aa[2]!.getAppArgs.back!
    unless pair.getAppFn.isConstOf ``Prod.mk do continue
    let pa := pair.getAppArgs
    let status := pa[pa.size-2]!
    let out := pa.back!
    unless ← withTransparency .reducible <| isDefEq (mkProj ``OwnedSdk 1 out)
        readArgs[readArgs.size-2]! do continue
    for priorRead in context do
      unless priorRead.type.isAppOfArity ``Eq 3 do continue
      let ra := priorRead.type.getAppArgs
      unless ra[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
      unless ra[2]!.getAppFn.isConstOf ``Result.ok do continue
      let saved ← saveState
      try
        let proof ← mkAppM ``acquired_read #[call[0]!,out,call[1]!,readArgs.back!,
          status,ra[2]!.getAppArgs.back!,mkFVar acquired.fvarId,mkFVar priorRead.fvarId]
        let term ← Term.exprToSyntax proof
        let cell ← mkFreshUserName `reborrowed
        let actual ← mkFreshUserName `reborrowRead
        let bytes ← mkFreshUserName `reborrowBytes
        evalTactic (← `(tactic| obtain ⟨$(mkIdent cell),$(mkIdent actual),$(mkIdent bytes)⟩ := $term))
        evalTactic (← `(tactic| rw [$(mkIdent actual):ident,bind_tc_ok,$(mkIdent bytes):ident]))
        return
      catch _ => saved.restore
  throwError "No matching reached acquisition and prior public read"

elab "borrowed_reduce" : tactic => withMainContext do
  let before ← getMainTarget
  evalTactic (← `(tactic| simp only [Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,bind_tc_ok]))
  if (← getGoals).isEmpty then return
  if (← getMainTarget)==before then throwError "No structural reduction"

/-- Complete emitted bodies, with the complete SDK and arbitrary Ops retained. -/
theorem body_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : Slice U8) (guards : LiveGuards) :
    BorrowedReference.owned_stage1_body ops program sdk data guards =
      owned_stage1_body ops program sdk data guards := by
  unfold BorrowedReference.owned_stage1_body owned_stage1_body
  run_tac logInfo "unfold complete"
  simp only [PrimitivesTotal.bytes_clone_total,BorrowedScan.scan_eq]
  run_tac logInfo "clone and scan normalization complete"
  repeat' first
    | borrowed_step
    | borrowed_frame
    | borrowed_reduce
  all_goals borrowed_step

#print axioms body_eq
end AspisS2OwnedStage1.SdkReference.BorrowedEquivalence
