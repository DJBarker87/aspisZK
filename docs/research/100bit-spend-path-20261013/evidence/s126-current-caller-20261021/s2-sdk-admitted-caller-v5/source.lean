import S2SdkGateAdmittedImageV1
import S2SdkProofGateJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.ProofGate

/-- The exact three reached native-shaped caller guard operations imply the
full-buffer reference gate result. Range/comparator/tag equality are tied to
one original Vec and candidate, never to separately selected byte carriers. -/
theorem caller_guard (proof : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (selected : Slice U8) (length : proof.val.length=58295)
    (range : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      proof {«end»:=688#usize}=ok selected)
    (compared : ProofPrefixParent.loopCmp selected candidate=ok false)
    (tag : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
      proof 696#usize=ok 2#u8) :
    reference_gate (alloc.vec.Vec.deref proof) candidate=
      ok (core.result.Result.Ok (688#usize,58295#usize)) := by
  obtain ⟨same,actualRange,cmp⟩ := caller_prefix_eq proof candidate length
  have sameSelected : same=selected := Result.ok.inj (actualRange.symm.trans range)
  subst same
  have prefixRun := cmp.trans compared
  have sum : (688#usize+57607#usize : Result Usize)=ok 58295#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  have checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
    unfold Usize.checked_add core.num.checked_add_UScalar
    rw [sum]; rfl
  have offset : (688#usize+8#usize : Result Usize)=ok 696#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  have lengthSlice : Slice.len (alloc.vec.Vec.deref proof)=58295#usize := by
    apply UScalar.eq_of_val_eq
    simpa [Slice.len,FrameOperationsTotal.deref_val] using length
  change Slice.index_usize (alloc.vec.Vec.deref proof) 696#usize=ok 2#u8 at tag
  simp [reference_gate,checked,lift,SourceInstallation.stdOption,
    core.result.Result.Insts.CoreOpsTry.branch,lengthSlice,prefixRun,offset,tag]


def GuardedFirst (ops : Ops) : Prop :=
  ∃ (proofData : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (pub : AspisS2OwnedStage1.Reachability.Public) (publicBytes proofBytes : Slice U8)
    (split : Usize) (checkpoint : alloc.vec.Vec U8),
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

private theorem gate_first_intro (ops : Ops)
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
    (length : proof.val.length=58295) (same : different=false) (tagEq : tagValue=2#u8) :
    GuardedFirst ops := by
  subst different; subst tagValue
  have gate := caller_guard proof candidate selected length range compared tag
  exact ⟨proof,candidate,pub,publicBytes,proofBytes,split,checkpoint,suffixRange,first,gate,
    fun j => admitted_seed_fixed (alloc.vec.Vec.deref proof) candidate gate j⟩

private theorem guard_offset : (688#usize+8#usize : Result Usize)=ok 696#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

private theorem guard_checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
  have sum : (688#usize+57607#usize : Result Usize)=ok 58295#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  unfold Usize.checked_add core.num.checked_add_UScalar
  rw [sum]; rfl

/-- Normalize only reached scalar constants and their tiny checked additions.
The parser, verifier, SDK and field arithmetic remain opaque. -/
elab "sdk_guard_scalar" : tactic => withMainContext do
  for decl in (← getLCtx) do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let lhs := decl.type.getAppArgs[1]!
    let head := lhs.getAppFn
    let allowed := (match head with | .proj ``Ops i _ => i==4 || i==7 || i==2 | _ => false) || head.isConstOf ``Ops.op4 || head.isConstOf ``Ops.op7 ||
      head.isConstOf ``Ops.op2 || head.isConstOf ``aspis_r1_cost_probe.transport.Variant.tag ||
      head.isConstOf ``HAdd.hAdd || head.isConstOf ``lift
    unless allowed do continue
    let before ← saveState
    try
      evalTactic (← `(tactic| simp only [guard_offset,guard_checked] at $(mkIdent decl.userName):ident))
      let after ← withMainContext do getLocalDeclFromUserName decl.userName
      if after.type != decl.type then return
      before.restore
    catch _ => before.restore
    let reduced ← withTransparency .all <| whnf lhs
    unless reduced.getAppFn.isConstOf ``Result.ok do continue
    let saved ← saveState
    try
      let type ← Term.exprToSyntax (← mkEq reduced decl.type.getAppArgs[2]!)
      evalTactic (← `(tactic| change $type at $(mkIdent decl.userName):ident))
      evalTactic (← `(tactic| cases $(mkIdent decl.userName):ident))
      return
    catch _ => saved.restore
  throwError "No reached scalar constant equation"

elab "sdk_finish_guarded" : tactic => withMainContext do
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
            let saved ← saveState
            try
              let witness ← mkAppM ``gate_first_intro #[call[0]!,proofData,compared[1]!,compared[0]!,
                ca[2]!.getAppArgs.back!,ta[2]!.getAppArgs.back!,call[1]!,call[2]!,call[3]!,call[4]!,checkpoint,
                mkFVar range.fvarId,mkFVar cmp.fvarId,mkFVar tag.fvarId,mkFVar suffix.fvarId,mkFVar first.fvarId]
              let term ← Term.exprToSyntax witness
              evalTactic (← `(tactic| refine $term ?_ ?_ ?_))
              evalTactic (← `(tactic| all_goals first
                | assumption
                | omega
                | simp_all only [alloc.vec.Vec.len,Slice.len,FrameOperationsTotal.deref_val]
                | (apply UScalar.eq_of_val_eq; omega)))
              return
            catch _ => saved.restore
  throwError "No complete same-buffer guard/first witness yet"

/-- ACCEPTED-ONLY: the enclosing complete installed SDK reference derives the
same-buffer proof gate and current first_decoded call together. It introduces
no independent prefix/tag, child success or initializer fixed-point premise. -/
theorem stage1_guarded_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (sdk sdkOut : OwnedSdk) (data : alloc.vec.Vec U8)
    (accepted : ProofPrefixParent.stage1 ops verifierOps program sdk data=ok (.Ok (),sdkOut)) :
    GuardedFirst (Installation.install ops verifierOps) := by
  unfold ProofPrefixParent.stage1 at accepted
  obtain ⟨body,hbody,accepted⟩ := bind_success _ _ _ accepted
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨finalSdk,hrelease,accepted⟩ := bind_success _ _ _ accepted
  have hs : status=core.result.Result.Ok () := (Prod.mk.inj (Result.ok.inj accepted)).1
  subst status
  unfold ProofPrefixParent.bodyWithPrefixCmp at hbody
  repeat' first
    | sdk_guard_scalar
    | sdk_constructor_evidence
    | sdk_finish_guarded
    | solve | cases hbody
    | sdk_case_evidence
    | sdk_peel hbody
    | sdk_split hbody
    | sdk_reduce hbody

#print axioms stage1_guarded_first
#print axioms caller_guard
end AspisS2OwnedStage1.SdkReference.ProofGate
