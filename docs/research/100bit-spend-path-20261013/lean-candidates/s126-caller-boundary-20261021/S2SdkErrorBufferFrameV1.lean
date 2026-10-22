import S2SdkBorrowedBufferFrameV1
import S2SdkOwnedGuardBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.ErrorBufferFrame
open GuardRelease GuardAcquire GuardFrame BorrowedBufferFrame

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem checkpoint_buffers (sdk out : OwnedSdk) (guards returned : LiveGuards)
    (slot : Usize) (status : core.result.Result Unit solana_program_error.ProgramError)
    (h : owned_acquire_checkpoint sdk guards slot=ok (status,out,returned)) :
    buffers out=buffers sdk := by
  have step := h
  unfold owned_acquire_checkpoint at step
  obtain ⟨first,read,_⟩ := bind_success _ _ _ step
  have valid := index_success_valid sdk.data_cells slot first read
  obtain ⟨cell,actual,run⟩ := BorrowTotal.checkpoint_acquire_total sdk guards slot valid
  split at run
  · cases run.symm.trans h
    rfl
  · cases run.symm.trans h
    exact counter_update_buffers sdk slot cell (-1)#isize valid actual

theorem shared_buffers (sdk out : OwnedSdk) (slot : Usize)
    (status : core.result.Result Unit solana_program_error.ProgramError)
    (h : owned_acquire_shared sdk slot=ok (status,out)) :
    buffers out=buffers sdk :=
  acquire_buffers sdk out slot status ((acquire_source_eq sdk slot).trans h)

theorem drop_shared_buffers (sdk out : OwnedSdk) (slot : Usize)
    (h : dropShared sdk slot=ok out) : buffers out=buffers sdk := by
  unfold dropShared at h
  obtain ⟨cell,_,h⟩ := bind_success _ _ _ h
  obtain ⟨option,_,h⟩ := bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := bind_success _ _ _ h
  obtain ⟨pair,index,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨old,back⟩
  cases h
  obtain ⟨valid,actual,setter⟩ := index_mut_success sdk slot old back index
  subst back
  exact counter_update_buffers sdk slot old next valid actual

theorem drop_checkpoint_buffers (sdk out : OwnedSdk) (slot : Usize)
    (h : dropCheckpoint sdk slot=ok out) : buffers out=buffers sdk := by
  unfold dropCheckpoint at h
  obtain ⟨cell,_,h⟩ := bind_success _ _ _ h
  obtain ⟨option,_,h⟩ := bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := bind_success _ _ _ h
  obtain ⟨pair,index,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨old,back⟩
  cases h
  obtain ⟨valid,actual,setter⟩ := index_mut_success sdk slot old back index
  subst back
  exact counter_update_buffers sdk slot old next valid actual

private def pairParts (value : Expr) : MetaM (Expr × Expr) := do
  let value ← instantiateMVars value
  unless value.getAppFn.isConstOf ``Prod.mk do throwError "Expected reached product"
  let args := value.getAppArgs
  return (args[args.size-2]!,args.back!)

private partial def frameChain (goal : Expr) (used : List FVarId := []) : MetaM Expr := do
  let args := goal.getAppArgs
  let left := args[1]!
  let right := args[2]!
  if ← withTransparency .reducible <| isDefEq left right then return ← mkEqRefl left
  for decl in (← getLCtx) do
    if used.contains decl.fvarId then continue
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let eq := decl.type.getAppArgs
    unless eq[1]!.getAppFn.isConstOf ``buffers do continue
    unless ← withTransparency .reducible <| isDefEq eq[1]! left do continue
    let saved ← saveState
    try
      let suffix ← frameChain (← mkEq eq[2]! right) (decl.fvarId::used)
      return ← mkAppM ``Eq.trans #[mkFVar decl.fvarId,suffix]
    catch _ => saved.restore
  throwError "No reached buffer-frame chain"

elab "sdk_buffer_chain" : tactic => withMainContext do
  let proof ← frameChain (← getMainTarget)
  (← getMainGoal).assign proof
  replaceMainGoal []

elab "sdk_buffer_facts" : tactic => withMainContext do
  for decl in (← getLCtx) do
    unless decl.type.isAppOfArity ``Eq 3 do continue
    let eq := decl.type.getAppArgs
    let lhs := eq[1]!
    unless eq[2]!.getAppFn.isConstOf ``Result.ok do continue
    let call := lhs.getAppArgs
    let saved ← saveState
    try
      let proof ←
        if lhs.getAppFn.isConstOf ``owned_acquire_checkpoint then do
          let (status,pair) ← pairParts eq[2]!.getAppArgs.back!
          let (out,returned) ← pairParts pair
          mkAppM ``checkpoint_buffers #[call[0]!,out,call[1]!,returned,call[2]!,status,mkFVar decl.fvarId]
        else if lhs.getAppFn.isConstOf ``owned_acquire_shared then do
          let (status,out) ← pairParts eq[2]!.getAppArgs.back!
          mkAppM ``shared_buffers #[call[0]!,out,call[1]!,status,mkFVar decl.fvarId]
        else if lhs.getAppFn.isConstOf ``dropShared || lhs.getAppFn.isConstOf ``dropCheckpoint then
          mkAppM (if lhs.getAppFn.isConstOf ``dropShared then ``drop_shared_buffers else ``drop_checkpoint_buffers)
            #[call[0]!,eq[2]!.getAppArgs.back!,call[1]!,mkFVar decl.fvarId]
        else throwError "Not an SDK counter operation"
      let type ← inferType proof
      if ← (← getLCtx).anyM (fun d => withTransparency .reducible <| isDefEq d.type type) then continue
      let next ← (← getMainGoal).assert (← mkFreshUserName `bufferFrame) type proof
      let (_,next) ← next.intro1
      replaceMainGoal [next]
      return
    catch _ => saved.restore
  throwError "No new reached buffer frame"

elab "sdk_buffer_step " h:ident : tactic => withMainContext do
  let decl ← (← getFVarId h).getDecl
  let args := decl.type.getAppArgs
  let lhs := args[1]!.consumeMData
  let rhs := args[2]!
  if let .letE _ _ value body _ := lhs then
    let type ← Term.exprToSyntax (← mkEq (body.instantiate1 value) rhs)
    evalTactic (← `(tactic| change $type at $h:ident))
    return
  if lhs.getAppFn.isConstOf ``Aeneas.Std.uncurry then
    evalTactic (← `(tactic| simp only [Aeneas.Std.uncurry] at $h:ident))
    return
  if lhs.getAppFn.isConstOf ``Result.ok then
    evalTactic (← `(tactic| cases $h:ident))
    evalTactic (← `(tactic| all_goals sdk_buffer_chain))
    return
  if lhs.getAppFn.isConstOf ``Result.fail || lhs.getAppFn.isConstOf ``Result.div then
    evalTactic (← `(tactic| cases $h:ident))
    return
  if lhs.getAppFn.isConstOf ``ite then
    evalTactic (← `(tactic| sdk_split $h:ident))
    return
  if lhs.getAppFn.isConstOf ``Bind.bind then
    evalTactic (← `(tactic| sdk_peel $h:ident))
    return
  if let some reduced ← reduceRecMatcher? lhs then
    let type ← Term.exprToSyntax (← mkEq reduced rhs)
    evalTactic (← `(tactic| change $type at $h:ident))
    return
  if let some matched ← matchMatcherApp? lhs true then
    for discriminant in matched.discrs do
      if discriminant.isFVar then
        let source ← discriminant.fvarId!.getDecl
        evalTactic (← `(tactic| cases $(mkIdent source.userName):ident))
        return
  throwError "Unsupported outer frame step"

/-- Every ordinary release return preserves all bytes, with no independently
assumed live-guard, valid-slot or arithmetic-range condition. -/
theorem release_buffers (sdk out : OwnedSdk) (guards : LiveGuards)
    (h : owned_release_guards sdk guards=ok out) : buffers out=buffers sdk := by
  rw [release_eq] at h
  rcases guards with ⟨checkpoint,pub,proof⟩
  cases proof <;> cases pub <;> cases checkpoint <;>
    try dsimp only at h
  all_goals repeat' first
    | sdk_buffer_chain
    | sdk_constructor_evidence
    | sdk_buffer_facts
    | sdk_buffer_step h

/-- Complete emitted body: an ordinary Err return preserves every buffer.
The sole bytes assignment lies on an Ok return. Arbitrary child operations
retain all errors/divergence; no child success or byte-frame premise is added. -/
theorem body_error_buffers (ops : Ops) (program : Array U8 32#usize)
    (sdk out : OwnedSdk) (data : Slice U8) (guards returned : LiveGuards)
    (error : solana_program_error.ProgramError)
    (h : owned_stage1_body ops program sdk data guards=ok (.Err error,out,returned)) :
    buffers out=buffers sdk := by
  unfold owned_stage1_body at h
  repeat' first
    | sdk_buffer_chain
    | sdk_buffer_facts
    | sdk_guard_status
    | sdk_buffer_step h

/-- The complete stage1, including its exact release finalizer, preserves all
buffer bytes on every ordinary rejected execution. This is a returned-error
frame theorem, not termination for arbitrary children or native SDK closure. -/
theorem stage1_error_buffers (ops : Ops) (program : Array U8 32#usize)
    (sdk out : OwnedSdk) (data : alloc.vec.Vec U8)
    (error : solana_program_error.ProgramError)
    (h : owned_stage1 ops program sdk data=ok (.Err error,out)) :
    buffers out=buffers sdk := by
  unfold owned_stage1 at h
  obtain ⟨body,bodyRun,h⟩ := bind_success _ _ _ h
  rcases body with ⟨status,sdkBody,guards⟩
  obtain ⟨sdkOut,releaseRun,h⟩ := bind_success _ _ _ h
  cases h
  exact (release_buffers sdkBody out guards releaseRun).trans
    (body_error_buffers ops program sdk sdkBody (alloc.vec.Vec.deref data) noGuards guards error bodyRun)

#print axioms checkpoint_buffers
#print axioms shared_buffers
#print axioms drop_shared_buffers
#print axioms drop_checkpoint_buffers
#print axioms release_buffers
#print axioms body_error_buffers
#print axioms stage1_error_buffers
end AspisS2OwnedStage1.SdkReference.ErrorBufferFrame
