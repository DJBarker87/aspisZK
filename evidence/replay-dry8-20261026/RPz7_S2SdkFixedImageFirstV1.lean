import RPz7_S2SdkCheckpointImageV1
import RPz7_S2SdkFixedSavedFirstV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open ProofGate.FixedLinked

private theorem fixed_bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Fixed initial input views, same decode/projection/first result, and final
checkpoint account bytes, obtained together from a complete stage1 success. -/
def FixedImageCall (initial out : OwnedSdk) (ops : Ops) : Prop :=
  ∃ (proofData : alloc.vec.Vec U8)
    (statement : AspisS2OwnedStage1.Reachability.Statement)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount),
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account ∧
    inputBytes initial 0#usize=ok (alloc.vec.Vec.deref proofData) ∧
    inputBytes initial 1#usize=ok publicBytes ∧
    decode_public_statement_box ops publicBytes=ok (.Ok statement) ∧
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok pub ∧
    proofData.val.length=58295 ∧
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proofData {start:=688#usize,«end»:=58295#usize}=ok proofBytes ∧
    first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint) ∧
    BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint ∧
    BorrowedBufferFrame.buffers out=(BorrowedBufferFrame.buffers initial).set account.data_slot.val checkpoint

private theorem fixed_intro (initial out : OwnedSdk) (ops : Ops)
    (proofData : alloc.vec.Vec U8) (statement : AspisS2OwnedStage1.Reachability.Statement)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8) (account : OwnedAccount)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account)
    (decoded : decode_public_statement_box ops publicBytes=ok (.Ok statement))
    (semantic : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement=ok pub)
    (range : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proofData {start:=688#usize,«end»:=58295#usize}=ok proofBytes)
    (first : first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint))
    (proofOrigin : inputBytes initial 0#usize=ok (alloc.vec.Vec.deref proofData))
    (publicOrigin : inputBytes initial 1#usize=ok publicBytes)
    (length : proofData.val.length=58295)
    (saved : BorrowedBufferFrame.readBytes out account.data_slot=ok checkpoint)
    (image : BorrowedBufferFrame.buffers out=(BorrowedBufferFrame.buffers initial).set account.data_slot.val checkpoint) :
    FixedImageCall initial out ops :=
  ⟨proofData,statement,pub,publicBytes,proofBytes,split,checkpoint,account,
    accountRead,proofOrigin,publicOrigin,decoded,semantic,length,range,first,saved,image⟩

private theorem proof_length (bytes : alloc.vec.Vec U8)
    (h : alloc.vec.Vec.len bytes=58295#usize) : bytes.val.length=58295 := by
  have value := congrArg UScalar.val h
  simpa [alloc.vec.Vec.len] using value

elab "sdk_fixed_image_finish" : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.getAppFn.isConstOf ``FixedImageCall do throwError "Expected FixedImageCall"
  let args := target.getAppArgs
  let context ← getLCtx
  let mut diagnostic : MessageData := m!"No first call"
  for first in context do
    unless first.type.isAppOfArity ``Eq 3 do continue
    let fa := first.type.getAppArgs
    unless fa[1]!.getAppFn.isConstOf ``first_decoded do continue
    unless fa[2]!.getAppFn.isConstOf ``Result.ok do continue
    let inner := fa[2]!.getAppArgs.back!
    unless inner.getAppFn.isConstOf ``core.result.Result.Ok do continue
    let cp := inner.getAppArgs.back!
    let call := fa[1]!.getAppArgs
    for semantic in context do
      unless semantic.type.isAppOfArity ``Eq 3 do continue
      let sa := semantic.type.getAppArgs
      unless sa[1]!.getAppFn.isConstOf ``aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public do continue
      unless sa[2]!.getAppFn.isConstOf ``Result.ok do continue
      unless ← withTransparency .reducible <| isDefEq sa[2]!.getAppArgs.back! call[1]! do continue
      let statement := sa[1]!.getAppArgs.back!
      for decoded in context do
        unless decoded.type.isAppOfArity ``Eq 3 do continue
        let da := decoded.type.getAppArgs
        unless da[1]!.getAppFn.isConstOf ``SdkReference.decode_public_statement_box do continue
        for range in context do
          unless range.type.isAppOfArity ``Eq 3 do continue
          let ra := range.type.getAppArgs
          unless ra[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
          unless ra[2]!.getAppFn.isConstOf ``Result.ok do continue
          unless ← withTransparency .reducible <| isDefEq ra[2]!.getAppArgs.back! call[3]! do continue
          let rc := ra[1]!.getAppArgs
          let proofData := rc[rc.size-2]!
          for accountRead in context do
            unless accountRead.type.isAppOfArity ``Eq 3 do continue
            let ar := accountRead.type.getAppArgs
            unless ar[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
            unless ar[2]!.getAppFn.isConstOf ``Result.ok do continue
            let account := ar[2]!.getAppArgs.back!
            unless ← isDefEq (← inferType account) (mkConst ``OwnedAccount) do continue
            let saved ← saveState
            try
              let intro ← mkAppM ``fixed_intro #[args[0]!,args[1]!,args[2]!,proofData,statement,call[1]!,call[2]!,call[3]!,call[4]!,cp,account,
                mkFVar accountRead.fvarId,mkFVar decoded.fvarId,mkFVar semantic.fvarId,mkFVar range.fvarId,mkFVar first.fvarId]
              let term ← Term.exprToSyntax intro
              evalTactic (← `(tactic| refine $term ?_ ?_ ?_ ?_ ?_))
              let goals ← getGoals
              unless goals.length==5 do throwError "Expected origins, length and saved bytes"
              for goal in goals.take 2 do
                setGoals [goal]
                evalTactic (← `(tactic| sdk_input_origin))
              setGoals [goals[2]!]
              evalTactic (← `(tactic| apply proof_length; assumption))
              setGoals [goals[3]!]
              evalTactic (← `(tactic| apply released_written_bytes <;> assumption))
              setGoals [goals[4]!]
              evalTactic (← `(tactic| apply released_written_image <;> first | assumption | sdk_buffer_chain))
              return
            catch err => saved.restore;diagnostic := err.toMessageData
  throwError m!"No fixed saved witness: {diagnostic}"

elab "sdk_fixed_image_return" h:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  unless decl.type.isAppOfArity ``Eq 3 do throwError "Expected body equation"
  let lhs ← whnf decl.type.getAppArgs[1]!
  unless lhs.getAppFn.isConstOf ``Result.ok do throwError "Not body return"
  let ty ← Term.exprToSyntax (← mkEq lhs decl.type.getAppArgs[2]!)
  evalTactic (← `(tactic| change $ty at $h:ident))
  evalTactic (← `(tactic| cases $h:ident))
  evalTactic (← `(tactic| sdk_fixed_image_finish))

/-- ACCEPTED-ONLY: one complete installed execution supplies the original
inputs, decoded statement, actual first output and saved final account bytes. -/
theorem stage1_fixed_image_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : ProofPrefixParent.stage1 ops verifierOps program initial data=ok (.Ok (),out)) :
    FixedImageCall initial out (Installation.install ops verifierOps) := by
  unfold ProofPrefixParent.stage1 at accepted
  obtain ⟨body,hbody,accepted⟩ := fixed_bind_success _ _ _ accepted
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,accepted⟩ := fixed_bind_success _ _ _ accepted
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
    | sdk_fixed_image_return hbody
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody

theorem owned_stage1_fixed_image_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps) program initial data=ok (.Ok (),out)) :
    FixedImageCall initial out (Installation.install ops verifierOps) := by
  apply stage1_fixed_image_first ops verifierOps program initial out data
  rw [ProofPrefixParent.stage1_eq]
  exact accepted

theorem borrowed_stage1_fixed_image_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial data=ok (.Ok (),out)) :
    FixedImageCall initial out (Installation.install ops verifierOps) := by
  apply owned_stage1_fixed_image_first ops verifierOps program initial out data
  rw [←BorrowedEquivalence.stage1_eq]
  exact accepted

#print axioms stage1_fixed_image_first
#print axioms owned_stage1_fixed_image_first
#print axioms borrowed_stage1_fixed_image_first
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
