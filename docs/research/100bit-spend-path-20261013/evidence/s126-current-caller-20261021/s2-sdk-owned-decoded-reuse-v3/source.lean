import S2SdkOwnedReachabilityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.DecodedReuse

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem decoded_call_intro (ops : SdkReference.Ops) (bytes : Slice U8)
    (statement : AspisS2OwnedStage1.Reachability.Statement)
    (pub : AspisS2OwnedStage1.Reachability.Public) (proof : Slice U8) (k : Usize)
    (checkpoint : alloc.vec.Vec U8)
    (hbox : decode_public_statement_box ops bytes=ok (.Ok statement))
    (hpub : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok pub)
    (hfirst : first_decoded ops pub bytes proof k=ok (.Ok checkpoint)) :
    ∃ (publicBytes : Slice U8) (decoded : AspisS2OwnedStage1.Reachability.Statement)
      (selected : AspisS2OwnedStage1.Reachability.Public) (proofBytes : Slice U8)
      (split : Usize) (out : alloc.vec.Vec U8),
      decode_public_statement_box ops publicBytes=ok (.Ok decoded) ∧
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        decoded=ok selected ∧
      first_decoded ops selected publicBytes proofBytes split=ok (.Ok out) :=
  ⟨bytes,statement,pub,proof,k,checkpoint,hbox,hpub,hfirst⟩

/-- Propagate concrete constructor equations left by Try::branch. Only
outer matchers and already pure results are reduced; source callees stay opaque. -/
elab "sdk_constructor_evidence" : tactic => withMainContext do
  for decl in (← getLCtx) do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let lhs := decl.type.getAppArgs[1]!
    unless lhs.getAppFn.isConstOf ``Result.ok || (← isMatcherApp lhs) do continue
    let reduced ← whnf lhs
    unless reduced.getAppFn.isConstOf ``Result.ok do continue
    let saved ← saveState
    try
      evalTactic (← `(tactic| cases $(mkIdent decl.userName):ident))
      return
    catch _ => saved.restore
  throwError "No concrete branch equation"

/-- The emitted parent must supply all three matching concrete call equations.
The helper introduces no execution premise into the enclosing theorem. -/
elab "sdk_finish_decoded" : tactic => withMainContext do
  let context := (← getLCtx)
  for first in context do
    let ft := first.type
    unless ft.isAppOfArity ``Eq 3 do continue
    let fa := ft.getAppArgs
    unless fa[1]!.getAppFn.isConstOf ``SdkReference.first_decoded do continue
    let call := fa[1]!.getAppArgs
    let rhs := fa[2]!
    unless rhs.getAppFn.isConstOf ``Result.ok do continue
    let inner := rhs.getAppArgs.back!
    unless inner.getAppFn.isConstOf ``core.result.Result.Ok do continue
    let checkpoint := inner.getAppArgs.back!
    for box in context do
      unless box.type.isAppOfArity ``Eq 3 do continue
      let ba := box.type.getAppArgs
      unless ba[1]!.getAppFn.isConstOf ``SdkReference.decode_public_statement_box do continue
      unless ba[2]!.getAppFn.isConstOf ``Result.ok do continue
      let bi := ba[2]!.getAppArgs.back!
      unless bi.getAppFn.isConstOf ``core.result.Result.Ok do continue
      let statement := bi.getAppArgs.back!
      for selected in context do
        unless selected.type.isAppOfArity ``Eq 3 do continue
        let sa := selected.type.getAppArgs
        unless sa[1]!.getAppFn.isConstOf
          ``aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public do continue
        let saved ← saveState
        try
          let proof ← mkAppM ``decoded_call_intro
            #[call[0]!,call[2]!,statement,call[1]!,call[3]!,call[4]!,checkpoint,
              mkFVar box.fvarId,mkFVar selected.fvarId,mkFVar first.fvarId]
          let term ← Term.exprToSyntax proof
          evalTactic (← `(tactic| exact $term))
          return
        catch _ => saved.restore
  throwError "Matching decoder/semantic/first equations not yet present"

/-- ACCEPTED-ONLY complete owned parent: the very same public byte slice is
boxed once, projected to the semantic public and passed to first_decoded.
No decode, projection or child-call success is independently assumed.
Real SDK buffer construction/correspondence remains a separate obligation. -/
theorem stage1_decoded_first (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (h : owned_stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    ∃ (publicBytes : Slice U8) (decoded : AspisS2OwnedStage1.Reachability.Statement)
      (selected : AspisS2OwnedStage1.Reachability.Public) (proofBytes : Slice U8)
      (split : Usize) (out : alloc.vec.Vec U8),
      decode_public_statement_box (Installation.install ops verifierOps) publicBytes=ok (.Ok decoded) ∧
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        decoded=ok selected ∧
      first_decoded (Installation.install ops verifierOps) selected publicBytes proofBytes split=ok (.Ok out) := by
  unfold owned_stage1 at h
  obtain ⟨body,hbody,h⟩ := bind_success _ _ _ h
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,h⟩ := bind_success _ _ _ h
  have hs : status=core.result.Result.Ok () := (Prod.mk.inj (Result.ok.inj h)).1
  subst status
  unfold owned_stage1_body at hbody
  repeat' first
    | sdk_constructor_evidence
    | sdk_finish_decoded
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody

/-- The current source first wrapper on the same bytes follows from the complete
owned stage1 execution. This consumes the already checked decoder-scoped reuse
transport; it does not posit another independent parse or semantic public. -/
theorem stage1_current_first (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (h : owned_stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    ∃ (publicBytes : Slice U8) (decoded : AspisR1TerminalDecoder.PublicBinding.Statement)
      (proofBytes : Slice U8) (split : Usize) (out : alloc.vec.Vec U8),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual publicBytes=ok (.Ok decoded) ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (SourceInstallation.currentDigest
          (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (fun e => ops.op11 (SourceInstallation.freshError e)) publicBytes proofBytes split=ok (.Ok out) := by
  obtain ⟨bytes,statement,pub,proof,k,cp,hbox,hpub,hfirst⟩ :=
    stage1_decoded_first ops verifierOps program sdk sdkOut data h
  rw [Installation.boxed_eq] at hbox
  have hactual := SourceInstallation.boxed_success
    (Installation.legacyHelperOps (Installation.install ops verifierOps)) bytes statement hbox
  change SourceInstallation.actualDecoder bytes=ok (.Ok statement) at hactual
  obtain ⟨decoded,hdecode,hstatement⟩ := SourceInstallation.decoder_success bytes statement hactual
  subst statement
  have hpublicSelection : CurrentCarrier.toCurrentPublic pub =
      AspisR1CurrentCaller.FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic decoded) := by
    have hp := CurrentCarrier.selected_public decoded
    rw [hpub] at hp
    exact Result.ok.inj hp
  have htx := Installation.first_success ops verifierOps pub bytes proof k cp hfirst
  rw [hpublicSelection] at htx
  refine ⟨bytes,decoded,proof,k,cp,hdecode,?_⟩
  unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
  rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ hdecode]
  unfold AspisR1PublicPreparation.RepinS6First.first_decoded
    AspisR1PublicPreparation.RepinS6First.observer
    AspisR1CurrentCaller.FirstComposition.currentTx1
  simp only [bind_tc_ok,Option.map_none,htx,
    AspisR1PublicPreparation.core.result.Result.map_err]

#print axioms stage1_current_first
#print axioms stage1_decoded_first
end AspisS2OwnedStage1.SdkReference.DecodedReuse
