import RPz7_S2SdkCheckpointWriterV1
import RPz7_S2SdkCheckpointLengthV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter

/-- One reached first call and the same returned checkpoint, in the original
account2 slot after complete finalization. No separately selected saved value. -/
def SizedSavedCall (initial out : OwnedSdk) (ops : Ops) : Prop :=
  ∃ (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount),
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account ∧
    first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint) ∧
    BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint ∧ checkpoint.val.length=1768

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem sized_intro (initial out : OwnedSdk) (ops : Ops)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount)
    (beforeWrite : alloc.vec.Vec U8) (header size : Usize)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account)
    (first : first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint))
    (headerRead : owned_data_len initial account.data_slot=ok (.Ok header))
    (sizeRead : aspis_r1_cost_probe.verifier.checkpoint_size .S2=ok size)
    (sameHeader : header=size)
    (sameLength : alloc.vec.Vec.len checkpoint=alloc.vec.Vec.len beforeWrite)
    (origin : ProofGate.FixedLinked.inputBytes initial 2#usize=ok (alloc.vec.Vec.deref beforeWrite))
    (saved : BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint) :
    SizedSavedCall initial out ops :=
  ⟨pub,publicBytes,proofBytes,split,checkpoint,account,accountRead,first,saved,
    checkpoint_length_from_calls initial account beforeWrite checkpoint header size
      accountRead origin headerRead sizeRead sameHeader sameLength⟩

elab "sdk_sized_saved_finish" : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.getAppFn.isConstOf ``SizedSavedCall do throwError m!"Expected SizedSavedCall, found {target}"
  let args := target.getAppArgs
  let initial := args[0]!
  let out := args[1]!
  let ops := args[2]!
  let context ← getLCtx
  let mut diagnostic : MessageData := m!"No source first success"
  for first in context do
    unless first.type.isAppOfArity ``Eq 3 do continue
    let fa := first.type.getAppArgs
    unless fa[1]!.getAppFn.isConstOf ``first_decoded do continue
    unless fa[2]!.getAppFn.isConstOf ``Result.ok do continue
    let inner := fa[2]!.getAppArgs.back!
    unless inner.getAppFn.isConstOf ``core.result.Result.Ok do continue
    diagnostic := m!"First found; no original account2 read"
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
      for headerRead in context do
        unless headerRead.type.isAppOfArity ``Eq 3 do continue
        let ha := headerRead.type.getAppArgs
        unless ha[1]!.getAppFn.isConstOf ``owned_data_len do continue
        unless ha[2]!.getAppFn.isConstOf ``Result.ok do continue
        let inner := ha[2]!.getAppArgs.back!
        unless inner.getAppFn.isConstOf ``core.result.Result.Ok do continue
        let header := inner.getAppArgs.back!
        for sizeRead in context do
          unless sizeRead.type.isAppOfArity ``Eq 3 do continue
          let sa := sizeRead.type.getAppArgs
          unless sa[1]!.getAppFn.isConstOf ``aspis_r1_cost_probe.verifier.checkpoint_size do continue
          unless sa[2]!.getAppFn.isConstOf ``Result.ok do continue
          let size := sa[2]!.getAppArgs.back!
          for cellRead in context do
            unless cellRead.type.isAppOfArity ``Eq 3 do continue
            let ca := cellRead.type.getAppArgs
            unless ca[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
            unless ca[2]!.getAppFn.isConstOf ``Result.ok do continue
            let cell := ca[2]!.getAppArgs.back!
            unless ← isDefEq (← inferType cell) (mkConst ``OwnedDataCell) do continue
            let saved ← saveState
            try
              let intro ← mkAppM ``sized_intro #[initial,out,ops,call[1]!,call[2]!,call[3]!,call[4]!,cp,account,
                mkProj ``OwnedDataCell 0 cell,header,size,mkFVar accountRead.fvarId,mkFVar first.fvarId,
                mkFVar headerRead.fvarId,mkFVar sizeRead.fvarId]
              let term ← Term.exprToSyntax intro
              evalTactic (← `(tactic| refine $term ?_ ?_ ?_ ?_))
              let goals ← getGoals
              unless goals.length==4 do throwError "Expected header/length/origin/saved goals"
              for goal in goals.take 2 do
                setGoals [goal];evalTactic (← `(tactic| assumption))
              setGoals [goals[2]!]
              evalTactic (← `(tactic| sdk_input_origin))
              setGoals [goals[3]!]
              evalTactic (← `(tactic| apply released_written_bytes <;> assumption))
              return
            catch err => saved.restore;diagnostic := err.toMessageData
  throwError m!"No complete source first/write/release witness: {diagnostic}"

elab "sdk_sized_saved_return" h:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  unless decl.type.isAppOfArity ``Eq 3 do throwError "Expected body equation"
  let lhs ← whnf decl.type.getAppArgs[1]!
  unless lhs.getAppFn.isConstOf ``Result.ok do throwError "Not the body return"
  let ty ← Term.exprToSyntax (← mkEq lhs decl.type.getAppArgs[2]!)
  evalTactic (← `(tactic| change $ty at $h:ident))
  evalTactic (← `(tactic| cases $h:ident))
  evalTactic (← `(tactic| sdk_sized_saved_finish))

/-- ACCEPTED-ONLY full caller: checkpoint retention after release is derived
from the same first_decoded result, not a writer or child-success premise. -/
theorem stage1_sized_saved_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : ProofPrefixParent.stage1 ops verifierOps program initial data=ok (.Ok (),out)) :
    SizedSavedCall initial out (Installation.install ops verifierOps) := by
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
    | sdk_sized_saved_return hbody
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody

theorem owned_stage1_sized_saved_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps) program initial data=ok (.Ok (),out)) :
    SizedSavedCall initial out (Installation.install ops verifierOps) := by
  apply stage1_sized_saved_first ops verifierOps program initial out data
  rw [ProofPrefixParent.stage1_eq]
  exact accepted

theorem borrowed_stage1_sized_saved_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial data=ok (.Ok (),out)) :
    SizedSavedCall initial out (Installation.install ops verifierOps) := by
  apply owned_stage1_sized_saved_first ops verifierOps program initial out data
  rw [←BorrowedEquivalence.stage1_eq]
  exact accepted

#print axioms stage1_sized_saved_first
#print axioms owned_stage1_sized_saved_first
#print axioms borrowed_stage1_sized_saved_first
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
