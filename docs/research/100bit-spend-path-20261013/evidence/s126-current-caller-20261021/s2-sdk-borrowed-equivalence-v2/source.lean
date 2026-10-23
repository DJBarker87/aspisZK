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
  let saved ← saveState
  if ← withTransparency .all <| isDefEq left right then
    (← getMainGoal).assign (← mkEqRefl left)
    replaceMainGoal []
    return
  saved.restore
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
    let m ← Term.exprToSyntax lm
    let f ← Term.exprToSyntax la.back!
    let g ← Term.exprToSyntax ra.back!
    evalTactic (← `(tactic| apply bind_congr_reached $m $f $g))
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
      | rw [if_pos $(mkIdent branch)]
      | rw [if_neg $(mkIdent branch)]))
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
  throwError "Unsupported outer equality: {left.getAppFn} / {right.getAppFn}"

/-- Complete emitted bodies, with the complete SDK and arbitrary Ops retained. -/
theorem body_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : Slice U8) (guards : LiveGuards) :
    BorrowedReference.owned_stage1_body ops program sdk data guards =
      owned_stage1_body ops program sdk data guards := by
  unfold BorrowedReference.owned_stage1_body owned_stage1_body
  simp only [PrimitivesTotal.bytes_clone_total,BorrowedScan.scan_eq]
  repeat' first
    | borrowed_step
    | progress simp only [Aeneas.Std.uncurry,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok]

#print axioms body_eq
end AspisS2OwnedStage1.SdkReference.BorrowedEquivalence
