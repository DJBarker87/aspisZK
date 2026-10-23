import S2SdkLinkedCallerV1
import S2SdkErrorBufferFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.ProofGate.FixedLinked
abbrev Statement := AspisS2OwnedStage1.Reachability.Statement
abbrev Common := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1

/-- Literal original input account byte view, retaining invalid account/slot errors. -/
def inputBytes (sdk : OwnedSdk) (index : Usize) : Result (Slice U8) := do
  let account ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
    sdk.accounts index
  let bytes ← BorrowedBufferFrame.readBytes sdk account.data_slot
  ok (alloc.vec.Vec.deref bytes)

theorem input_from_cell (initial current : OwnedSdk) (index : Usize)
    (account : OwnedAccount) (cell : OwnedDataCell)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts index=ok account)
    (cellRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      current.data_cells account.data_slot=ok cell)
    (frame : BorrowedBufferFrame.buffers current=BorrowedBufferFrame.buffers initial) :
    inputBytes initial index=ok (alloc.vec.Vec.deref cell.bytes) := by
  have currentRead : BorrowedBufferFrame.readBytes current account.data_slot=ok cell.bytes := by
    simp only [BorrowedBufferFrame.readBytes,cellRead,bind_tc_ok]
  have initialRead := (BorrowedBufferFrame.readBytes_eq initial current account.data_slot frame).symm.trans currentRead
  simp only [inputBytes,accountRead,initialRead,bind_tc_ok]

/-- Same decoder/encoder/gate/first witness, now tied to the FIXED initial SDK
account0/account1 byte views. These equations are conclusions of full installed
caller success, not additional input-byte or snapshot premises. -/
def LinkedFirst (initial : OwnedSdk) (ops : Ops) : Prop :=
  ∃ (proofData : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (decoded : Statement) (common : Common)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8),
    inputBytes initial 0#usize=ok (alloc.vec.Vec.deref proofData) ∧
    inputBytes initial 1#usize=ok publicBytes ∧
    decode_public_statement_box ops publicBytes=ok (.Ok decoded) ∧
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
      decoded=ok common ∧
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      decoded=ok pub ∧
    ops.op8 common.lane_transition.candidate_afterstate=ok (.Ok candidate) ∧
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proofData {start:=688#usize,«end»:=58295#usize}=ok proofBytes ∧
    first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint) ∧
    reference_gate (alloc.vec.Vec.deref proofData) candidate=
      ok (core.result.Result.Ok (688#usize,58295#usize)) ∧
    ∀ j,seedCell (alloc.vec.Vec.deref proofData) candidate j=proofData.val[j]?

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem linked_intro (initial : OwnedSdk) (ops : Ops)
    (proof : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (selected : Slice U8) (different : Bool) (tagValue : U8)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8)
    (range : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      proof {«end»:=688#usize}=ok selected)
    (compared : ProofPrefixParent.loopCmp selected candidate=ok different)
    (tag : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
      proof 696#usize=ok tagValue)
    (suffixRange : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=688#usize,«end»:=58295#usize}=ok proofBytes)
    (first : first_decoded ops pub publicBytes proofBytes split=ok (.Ok checkpoint))
    (decoded : Statement) (common : Common)
    (boxed : decode_public_statement_box ops publicBytes=ok (.Ok decoded))
    (commonCall : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
      decoded=ok common)
    (semantic : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      decoded=ok pub)
    (encoded : ops.op8 common.lane_transition.candidate_afterstate=ok (.Ok candidate))
    (length : proof.val.length=58295) (same : different=false) (tagEq : tagValue=2#u8)
    (proofOrigin : inputBytes initial 0#usize=ok (alloc.vec.Vec.deref proof))
    (publicOrigin : inputBytes initial 1#usize=ok publicBytes) :
    LinkedFirst initial ops := by
  subst different; subst tagValue
  have gate := caller_guard proof candidate selected length range compared tag
  exact ⟨proof,candidate,decoded,common,pub,publicBytes,proofBytes,split,checkpoint,proofOrigin,publicOrigin,boxed,commonCall,semantic,encoded,suffixRange,first,gate,
    fun j => admitted_seed_fixed (alloc.vec.Vec.deref proof) candidate gate j⟩

private theorem linked_length_of_len (bytes : alloc.vec.Vec U8)
    (h : alloc.vec.Vec.len bytes=58295#usize) : bytes.val.length=58295 := by
  have value := congrArg UScalar.val h
  simpa [alloc.vec.Vec.len] using value

/-- Preserve the original error mapper; reduce only a reached pure Result
map whose constructor is already known, to retain its exact encoder output. -/
elab "sdk_linked_map" : tactic => withMainContext do
  for decl in (← getLCtx) do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let lhs := decl.type.getAppArgs[1]!
    unless lhs.getAppFn.isConstOf ``core.result.Result.map_err do continue
    let reduced ← whnf lhs
    unless reduced.getAppFn.isConstOf ``Result.ok do continue
    let saved ← saveState
    try
      let ty ← Term.exprToSyntax (← mkEq reduced decl.type.getAppArgs[2]!)
      evalTactic (← `(tactic| change $ty at $(mkIdent decl.userName):ident))
      evalTactic (← `(tactic| cases $(mkIdent decl.userName):ident))
      return
    catch _ => saved.restore
  throwError "No reached constructor-known map_err equation"

/-- Only the emitted clone identity is reduced, before following provenance. -/
elab "sdk_input_clone" : tactic => withMainContext do
  for decl in (← getLCtx) do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let eq := decl.type.getAppArgs
    unless eq[1]!.getAppFn.isConstOf ``alloc.vec.CloneVec.clone do continue
    let saved ← saveState
    try
      evalTactic (← `(tactic| rw [PrimitivesTotal.bytes_clone_total] at $(mkIdent decl.userName):ident))
      evalTactic (← `(tactic| cases $(mkIdent decl.userName):ident))
      return
    catch _ => saved.restore
  throwError "No reached byte clone"

/-- Find the reached original account read and cell read, then discharge the
whole buffer-frame chain through actual reached acquisition postconditions. -/
elab "sdk_input_origin" : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.isAppOfArity ``Eq 3 do throwError "Not an input origin"
  let t := target.getAppArgs
  unless t[1]!.getAppFn.isConstOf ``inputBytes do throwError "Not an input view"
  unless t[2]!.getAppFn.isConstOf ``Result.ok do throwError "Not a successful input view"
  let initial := t[1]!.getAppArgs[0]!
  let index := t[1]!.getAppArgs[1]!
  let selected := t[2]!.getAppArgs.back!
  let context ← getLCtx
  for accountRead in context do
    unless accountRead.type.isAppOfArity ``Eq 3 do continue
    let ar := accountRead.type.getAppArgs
    unless ar[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
    unless ar[2]!.getAppFn.isConstOf ``Result.ok do continue
    let acall := ar[1]!.getAppArgs
    unless ← withTransparency .reducible <| isDefEq acall.back! index do continue
    unless ← withTransparency .reducible <| isDefEq acall[acall.size-2]! (mkProj ``OwnedSdk 0 initial) do continue
    let account := ar[2]!.getAppArgs.back!
    for cellRead in context do
      unless cellRead.type.isAppOfArity ``Eq 3 do continue
      let cr := cellRead.type.getAppArgs
      unless cr[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
      unless cr[2]!.getAppFn.isConstOf ``Result.ok do continue
      let ccall := cr[1]!.getAppArgs
      unless ← withTransparency .reducible <| isDefEq ccall.back! (mkProj ``OwnedAccount 6 account) do continue
      let cell := cr[2]!.getAppArgs.back!
      let saved ← saveState
      try
        let bytes ← mkAppM ``alloc.vec.Vec.deref #[mkProj ``OwnedDataCell 0 cell]
        unless ← withTransparency .reducible <| isDefEq selected bytes do throwError "Different byte view"
        let vec := ccall[ccall.size-2]!
        let .proj typeName field current := vec | throwError "Not a heap cell read"
        unless typeName == ``OwnedSdk && field == 1 do throwError "Not a heap cell projection"
        let proof ← mkAppM ``input_from_cell #[initial,current,index,account,cell,
          mkFVar accountRead.fvarId,mkFVar cellRead.fvarId]
        let term ← Term.exprToSyntax proof
        evalTactic (← `(tactic| refine $term ?_))
        let frameGoal ← getMainTarget
        unless frameGoal.isAppOfArity ``Eq 3 do throwError "Expected buffer equality after origin application"
        evalTactic (← `(tactic| sdk_buffer_chain))
        return
      catch _ => saved.restore
  throwError "No fixed original account/cell/frame provenance"

elab "sdk_finish_fixed_linked" : tactic => withMainContext do
  let context ← getLCtx
  let mut diagnostic : MessageData := m!"No successful first call"
  for first in context do
    unless first.type.isAppOfArity ``Eq 3 do continue
    let fa := first.type.getAppArgs
    unless fa[1]!.getAppFn.isConstOf ``SdkReference.first_decoded do continue
    let call := fa[1]!.getAppArgs
    unless fa[2]!.getAppFn.isConstOf ``Result.ok do continue
    let inner := fa[2]!.getAppArgs.back!
    unless inner.getAppFn.isConstOf ``core.result.Result.Ok do continue
    let checkpoint := inner.getAppArgs.back!
    let mut sources : Array (Expr × Expr × Expr × Expr × Expr) := #[]
    for semantic in context do
      unless semantic.type.isAppOfArity ``Eq 3 do continue
      let sa := semantic.type.getAppArgs
      unless sa[1]!.getAppFn.isConstOf
        ``aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public do continue
      unless sa[2]!.getAppFn.isConstOf ``Result.ok do continue
      unless ← withTransparency .reducible <| isDefEq sa[2]!.getAppArgs.back! call[1]! do continue
      let decoded := sa[1]!.getAppArgs.back!
      for boxed in context do
        unless boxed.type.isAppOfArity ``Eq 3 do continue
        let ba := boxed.type.getAppArgs
        unless ba[1]!.getAppFn.isConstOf ``SdkReference.decode_public_statement_box do continue
        unless ba[2]!.getAppFn.isConstOf ``Result.ok do continue
        let inside := ba[2]!.getAppArgs.back!
        unless inside.getAppFn.isConstOf ``core.result.Result.Ok do continue
        unless ← withTransparency .reducible <| isDefEq inside.getAppArgs.back! decoded do continue
        unless ← withTransparency .reducible <| isDefEq ba[1]!.getAppArgs.back! call[2]! do continue
        for common in context do
          unless common.type.isAppOfArity ``Eq 3 do continue
          let ca := common.type.getAppArgs
          unless ca[1]!.getAppFn.isConstOf
            ``aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common do continue
          unless ca[2]!.getAppFn.isConstOf ``Result.ok do continue
          unless ← withTransparency .reducible <| isDefEq ca[1]!.getAppArgs.back! decoded do continue
          sources := sources.push (decoded,ca[2]!.getAppArgs.back!,mkFVar boxed.fvarId,mkFVar common.fvarId,mkFVar semantic.fvarId)
    diagnostic := m!"Fixed source candidates: {sources.size}"
    unless sources.size==1 do continue
    let (decoded,common,boxed,commonCall,semantic) := sources[0]!
    for cmp in context do
      unless cmp.type.isAppOfArity ``Eq 3 do continue
      let ca := cmp.type.getAppArgs
      unless ca[1]!.getAppFn.isConstOf ``ProofPrefixParent.loopCmp do continue
      unless ca[2]!.getAppFn.isConstOf ``Result.ok do continue
      let compared := ca[1]!.getAppArgs
      for range in context do
        unless range.type.isAppOfArity ``Eq 3 do continue
        let ra := range.type.getAppArgs
        unless ra[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
        unless ra[2]!.getAppFn.isConstOf ``Result.ok do continue
        unless ← withTransparency .reducible <| isDefEq ra[2]!.getAppArgs.back! compared[0]! do continue
        let rangecall := ra[1]!.getAppArgs
        let proofData := rangecall[rangecall.size-2]!
        for tag in context do
          unless tag.type.isAppOfArity ``Eq 3 do continue
          let ta := tag.type.getAppArgs
          unless ta[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
          unless ta[2]!.getAppFn.isConstOf ``Result.ok do continue
          unless ← withTransparency .reducible <| isDefEq (← inferType ta[2]!.getAppArgs.back!) (mkConst ``U8) do continue
          let tagcall := ta[1]!.getAppArgs
          unless ← withTransparency .reducible <| isDefEq tagcall[tagcall.size-2]! proofData do continue
          for suffix in context do
            unless suffix.type.isAppOfArity ``Eq 3 do continue
            let sa := suffix.type.getAppArgs
            unless sa[1]!.getAppFn.isConstOf ``alloc.vec.Vec.index do continue
            unless sa[2]!.getAppFn.isConstOf ``Result.ok do continue
            unless ← withTransparency .reducible <| isDefEq sa[2]!.getAppArgs.back! call[3]! do continue
            for encoded in context do
              unless encoded.type.isAppOfArity ``Eq 3 do continue
              let ea := encoded.type.getAppArgs
              unless ea[2]!.getAppFn.isConstOf ``Result.ok do continue
              let inside := ea[2]!.getAppArgs.back!
              unless inside.getAppFn.isConstOf ``core.result.Result.Ok do continue
              unless ← withTransparency .reducible <| isDefEq inside.getAppArgs.back! compared[1]! do continue
              let saved ← saveState
              try
                logInfo "Fixed guard and source witness found"
                let target := (← getMainTarget).consumeMData
                unless target.getAppArgs.size == 2 do throwError "Expected fixed initial SDK and Ops arguments"
                let initial := target.getAppArgs[0]!
                let witness ← mkAppM ``linked_intro #[initial,call[0]!,proofData,compared[1]!,compared[0]!,
                  ca[2]!.getAppArgs.back!,ta[2]!.getAppArgs.back!,call[1]!,call[2]!,call[3]!,call[4]!,checkpoint,
                  mkFVar range.fvarId,mkFVar cmp.fvarId,mkFVar tag.fvarId,mkFVar suffix.fvarId,mkFVar first.fvarId,decoded,common,boxed,commonCall,semantic,mkFVar encoded.fvarId]
                let term ← Term.exprToSyntax witness
                evalTactic (← `(tactic| refine $term ?_ ?_ ?_ ?_ ?_))
                let goals ← getGoals
                unless goals.length ≥ 5 do throwError "Expected three scalar and two origin goals"
                for goal in goals.take 3 do
                  setGoals [goal]
                  evalTactic (← `(tactic| first
                    | assumption
                    | omega
                    | (apply linked_length_of_len; assumption)
                    | (apply Bool.eq_false_iff.mpr; assumption)
                    | (apply UScalar.eq_of_val_eq; omega)))
                for goal in (goals.drop 3).take 2 do
                  setGoals [goal]
                  evalTactic (← `(tactic| sdk_input_origin))
                setGoals (goals.drop 5)
                return
              catch err =>
                saved.restore
                diagnostic := m!"Fixed input witness not complete: {err.toMessageData}"
  throwError diagnostic

/-- ACCEPTED-ONLY: the enclosing complete installed SDK reference derives the
same-buffer decoder/semantic/encoder/proof gate and first_decoded call together. It introduces
no independent prefix/tag, child success or initializer fixed-point premise. -/
theorem stage1_linked_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : ProofPrefixParent.stage1 ops verifierOps program sdk data=ok (.Ok (),sdkOut)) :
    LinkedFirst sdk (Installation.install ops verifierOps) := by
  unfold ProofPrefixParent.stage1 at accepted
  obtain ⟨body,hbody,accepted⟩ := bind_success _ _ _ accepted
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,accepted⟩ := bind_success _ _ _ accepted
  have hs : status=core.result.Result.Ok () := (Prod.mk.inj (Result.ok.inj accepted)).1
  subst status
  unfold ProofPrefixParent.bodyWithPrefixCmp at hbody
  repeat' first
    | sdk_input_clone
    | sdk_buffer_facts
    | sdk_guard_condition
    | sdk_guard_scalar
    | sdk_linked_map
    | sdk_constructor_evidence
    | sdk_finish_fixed_linked
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody
  all_goals sdk_finish_fixed_linked

/-- Same full finalizer and original installed owned reference; no independent
child execution, statement, encoder output or buffer-match premise is added. -/
theorem owned_stage1_linked_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    LinkedFirst sdk (Installation.install ops verifierOps) := by
  apply stage1_linked_first ops verifierOps program sdk sdkOut data
  rw [ProofPrefixParent.stage1_eq]
  exact accepted

#print axioms input_from_cell
#print axioms stage1_linked_first
#print axioms owned_stage1_linked_first
end AspisS2OwnedStage1.SdkReference.ProofGate.FixedLinked
