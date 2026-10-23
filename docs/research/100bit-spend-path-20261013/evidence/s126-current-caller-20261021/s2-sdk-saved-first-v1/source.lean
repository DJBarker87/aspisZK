import S2SdkCheckpointWriterV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter

/-- One reached first call and the same returned checkpoint, in the original
account2 slot after complete finalization. No separately selected saved value. -/
def SavedCall (initial out : OwnedSdk) (ops : Ops) : Prop :=
  ∃ (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount),
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account ∧
    first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint) ∧
    BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem saved_intro (initial out : OwnedSdk) (ops : Ops)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account)
    (first : first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint))
    (saved : BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint) :
    SavedCall initial out ops :=
  ⟨pub,publicBytes,proofBytes,split,checkpoint,account,accountRead,first,saved⟩

elab "sdk_saved_finish" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.getAppFn.isConstOf ``SavedCall do throwError "Expected SavedCall"
  let args := target.getAppArgs
  let initial := args[0]!
  let out := args[1]!
  let ops := args[2]!
  let context ← getLCtx
  for first in context do
    unless first.type.isAppOfArity ``Eq 3 do continue
    let fa := first.type.getAppArgs
    unless fa[1]!.getAppFn.isConstOf ``first_decoded do continue
    unless fa[2]!.getAppFn.isConstOf ``Result.ok do continue
    let inner := fa[2]!.getAppArgs.back!
    unless inner.getAppFn.isConstOf ``core.result.Result.Ok do continue
    let cp := inner.getAppArgs.back!
    let call := fa[1]!.getAppArgs
    for accountRead in context do
      unless accountRead.type.isAppOfArity ``Eq 3 do continue
      let ar := accountRead.type.getAppArgs
      unless ar[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
      unless ar[2]!.getAppFn.isConstOf ``Result.ok do continue
      let account := ar[2]!.getAppArgs.back!
      unless ← isDefEq (← inferType account) (mkConst ``OwnedAccount) do continue
      let acall := ar[1]!.getAppArgs
      unless ← withTransparency .reducible <| isDefEq acall[acall.size-2]! (mkProj ``OwnedSdk 0 initial) do continue
      let saved ← saveState
      try
        let intro ← mkAppM ``saved_intro #[initial,out,ops,call[1]!,call[2]!,call[3]!,call[4]!,cp,account,mkFVar accountRead.fvarId,mkFVar first.fvarId]
        let term ← Term.exprToSyntax intro
        evalTactic (← `(tactic| refine $term ?_))
        evalTactic (← `(tactic| apply released_written_bytes <;> assumption))
        return
      catch _ => saved.restore
  throwError "No complete source first/write/release witness"

elab "sdk_saved_return" h:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  unless decl.type.isAppOfArity ``Eq 3 do throwError "Expected body equation"
  let lhs := decl.type.getAppArgs[1]!
  unless lhs.getAppFn.isConstOf ``Result.ok do throwError "Not the body return"
  evalTactic (← `(tactic| cases $h:ident))
  evalTactic (← `(tactic| sdk_saved_finish))

/-- ACCEPTED-ONLY full caller: checkpoint retention after release is derived
from the same first_decoded result, not a writer or child-success premise. -/
theorem stage1_saved_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : ProofPrefixParent.stage1 ops verifierOps program initial data=ok (.Ok (),out)) :
    SavedCall initial out (Installation.install ops verifierOps) := by
  unfold ProofPrefixParent.stage1 at accepted
  obtain ⟨body,hbody,accepted⟩ := bind_success _ _ _ accepted
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,accepted⟩ := bind_success _ _ _ accepted
  have hs : status=core.result.Result.Ok () := (Prod.mk.inj (Result.ok.inj accepted)).1
  have ho : finalSdk=out := (Prod.mk.inj (Result.ok.inj accepted)).2
  subst status
  subst finalSdk
  unfold ProofPrefixParent.bodyWithPrefixCmp at hbody
  repeat' first
    | sdk_input_clone
    | sdk_buffer_facts
    | sdk_guard_condition
    | sdk_guard_scalar
    | sdk_linked_map
    | sdk_constructor_evidence
    | sdk_saved_return hbody
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody
  all_goals sdk_saved_finish

#print axioms stage1_saved_first
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
