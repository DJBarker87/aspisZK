import S2SdkAdmittedCallerV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.ProofGate.Linked
abbrev Statement := AspisS2OwnedStage1.Reachability.Statement
abbrev Common := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def LinkedFirst (ops : Ops) : Prop :=
  ∃ (proofData : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (decoded : Statement) (common : Common)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8),
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

private theorem linked_intro (ops : Ops)
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
    (length : proof.val.length=58295) (same : different=false) (tagEq : tagValue=2#u8) :
    LinkedFirst ops := by
  subst different; subst tagValue
  have gate := caller_guard proof candidate selected length range compared tag
  exact ⟨proof,candidate,decoded,common,pub,publicBytes,proofBytes,split,checkpoint,boxed,commonCall,semantic,encoded,suffixRange,first,gate,
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

elab "sdk_finish_linked" : tactic => withMainContext do
  let context ← getLCtx
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
                let witness ← mkAppM ``linked_intro #[call[0]!,proofData,compared[1]!,compared[0]!,
                  ca[2]!.getAppArgs.back!,ta[2]!.getAppArgs.back!,call[1]!,call[2]!,call[3]!,call[4]!,checkpoint,
                  mkFVar range.fvarId,mkFVar cmp.fvarId,mkFVar tag.fvarId,mkFVar suffix.fvarId,mkFVar first.fvarId,decoded,common,boxed,commonCall,semantic,mkFVar encoded.fvarId]
                let term ← Term.exprToSyntax witness
                evalTactic (← `(tactic| refine $term ?_ ?_ ?_))
                evalTactic (← `(tactic| all_goals first
                  | assumption
                  | omega
                  | (apply linked_length_of_len; assumption)
                  | (apply Bool.eq_false_iff.mpr; assumption)
                  | (apply UScalar.eq_of_val_eq; omega)))
                return
              catch _ => saved.restore
  throwError "No complete same-buffer guard/first witness yet"

/-- ACCEPTED-ONLY: the enclosing complete installed SDK reference derives the
same-buffer decoder/semantic/encoder/proof gate and first_decoded call together. It introduces
no independent prefix/tag, child success or initializer fixed-point premise. -/
theorem stage1_linked_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : ProofPrefixParent.stage1 ops verifierOps program sdk data=ok (.Ok (),sdkOut)) :
    LinkedFirst (Installation.install ops verifierOps) := by
  unfold ProofPrefixParent.stage1 at accepted
  obtain ⟨body,hbody,accepted⟩ := bind_success _ _ _ accepted
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,accepted⟩ := bind_success _ _ _ accepted
  have hs : status=core.result.Result.Ok () := (Prod.mk.inj (Result.ok.inj accepted)).1
  subst status
  unfold ProofPrefixParent.bodyWithPrefixCmp at hbody
  repeat' first
    | sdk_guard_condition
    | sdk_guard_scalar
    | sdk_linked_map
    | sdk_constructor_evidence
    | sdk_finish_linked
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody

/-- Same full finalizer and original installed owned reference; no independent
child execution, statement, encoder output or buffer-match premise is added. -/
theorem owned_stage1_linked_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : owned_stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    LinkedFirst (Installation.install ops verifierOps) := by
  apply stage1_linked_first ops verifierOps program sdk sdkOut data
  rw [ProofPrefixParent.stage1_eq]
  exact accepted

#print axioms stage1_linked_first
#print axioms owned_stage1_linked_first
end AspisS2OwnedStage1.SdkReference.ProofGate.Linked
