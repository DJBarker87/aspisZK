import S2SdkOwnedInstallationV1
import Lean
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.Reachability

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private partial def sdkUnpackProduct (hypName : Name) : TacticM Unit := do
  let decl ← getLocalDeclFromUserName hypName
  let ty ← whnf decl.type
  if ty.getAppFn.isConstOf ``Prod then
    let lhsName ← mkFreshUserName `part
    let rhsName ← mkFreshUserName `part
    evalTactic (← `(tactic| rcases $(mkIdent hypName) with ⟨$(mkIdent lhsName),$(mkIdent rhsName)⟩))
    sdkUnpackProduct lhsName
    sdkUnpackProduct rhsName

/-- Invert only the outer successful bind. Callee implementations stay opaque;
this does not normalize parsers, fields, arrays, or concrete recurrences. -/
elab "sdk_peel " h:ident : tactic => do
  let before ← getLocalDeclFromUserName h.getId
  let value ← mkFreshUserName `value
  let called ← mkFreshUserName `called
  evalTactic (← `(tactic| obtain ⟨$(mkIdent value),$(mkIdent called),$h⟩ := bind_success _ _ _ $h))
  sdkUnpackProduct value
  let after ← getLocalDeclFromUserName h.getId
  if before.type == after.type then throwError "No successful bind was removed"

elab "sdk_reduce " h:ident : tactic => do
  let before ← getLocalDeclFromUserName h.getId
  evalTactic (← `(tactic| simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,bind_tc_ok] at $h:ident))
  let after ← getLocalDeclFromUserName h.getId
  if before.type == after.type then throwError "No structural reduction"

elab "sdk_finish_first" : tactic => do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOfArity ``Eq 3 then
      let args := ty.getAppArgs
      if args[1]!.getAppFn.isConstOf ``SdkReference.first_decoded then
        let saved ← saveState
        try
          evalTactic (← `(tactic| exact ⟨_,_,_,_,_,Installation.first_success ops verifierOps
            _ _ _ _ _ $(mkIdent decl.userName)⟩))
          return
        catch _ => saved.restore
  throwError "No successful concrete first_decoded witness yet"

/-- ACCEPTED-ONLY complete owned SDK parent reachability. The actual tx1/None
call follows from one complete owned-stage1 success; it is not a supplied
child execution. This is still a reference theorem: real SDK heap/snapshot
construction and its complete source/trace correspondence remain obligations. -/
theorem stage1_current_call (ops : SdkReference.Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (h : owned_stage1 (Installation.install ops verifierOps) program sdk data=ok (.Ok (),sdkOut)) :
    ∃ (pub : AspisS2OwnedStage1.Reachability.Public) (bytes proof : Slice U8)
      (k : Usize) (checkpoint : alloc.vec.Vec U8),
      AspisR1CurrentCaller.verifier.candidate.tx1 verifierOps
        (SourceInstallation.currentDigest
          (SdkReference.SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops verifierOps)))
        (CurrentCarrier.toCurrentPublic pub) bytes proof k () none=ok (.Ok checkpoint) := by
  unfold owned_stage1 at h
  obtain ⟨body,hbody,h⟩ := bind_success _ _ _ h
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,h⟩ := bind_success _ _ _ h
  have hs : status=core.result.Result.Ok () := (Prod.mk.inj (Result.ok.inj h)).1
  subst status
  unfold owned_stage1_body at hbody
  repeat' first
    | sdk_finish_first
    | solve | cases hbody
    | sdk_peel hbody
    | split at hbody
    | sdk_reduce hbody

#print axioms stage1_current_call
end AspisS2OwnedStage1.SdkReference.Reachability
