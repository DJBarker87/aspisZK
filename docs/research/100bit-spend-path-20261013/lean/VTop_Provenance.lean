import VTop_Entry

/-! Successful preparation/query/flush cuts only. This predicate contains no
checkpoint result, encoding, header or whole-caller acceptance conclusion. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Provenance
open Aeneas Aeneas.Std Result VTop_Stages

elab "vtop_prefix_witnesses" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let findSourceEq : Lean.Name → Lean.MetaM (Lean.Expr × Lean.Expr) := fun opName => do
      for decl in ← Lean.getLCtx do
        let typ := decl.type
        if typ.isAppOfArity ``Eq 3 then
          let args := typ.getAppArgs
          if args[1]!.getAppFn.isConstOf opName then
            return (args[1]!, args[2]!.getAppArgs.back!)
      throwError "missing source operation {opName}"
    let (_,zero) ← findSourceEq ``VTop_Stages.Ops.op1
    let (_,prepared) ← findSourceEq ``VTop_Stages.Ops.op7
    let g ← Lean.Meta.mkAppM ``Prod.snd #[prepared]
    let preparation ← Lean.Meta.mkAppM ``Prod.fst #[prepared]
    let (_,initial) ← findSourceEq ``VTop_Stages.Ops.op12
    let (batch,_) ← findSourceEq ``VTop_Stages.Ops.op5
    let root := batch.getAppArgs[batch.getAppArgs.size-3]!
    let (_,geometry) ← findSourceEq ``VTop_Stages.Ops.op11
    let (_,pending) ← findSourceEq ``VTop_Stages.Ops.op10
    let (_,returned) ← findSourceEq ``VTop_Stages.Ops.op6
    let (_,flushed) ← findSourceEq ``VTop_Stages.Ops.op9
    let (_,parsed) ← findSourceEq ``VTop_Stages.Ops.op3
    let (_,splitValue) ← findSourceEq ``VTop_Stages.Ops.op16
    let inner (e : Lean.Expr) := e.getAppArgs.back!
    let values := #[zero,g,preparation,inner initial,root,inner geometry,
      inner pending,inner returned,flushed,inner parsed,splitValue]
    let mut current := goal
    for value in values do
      let target ← Lean.Meta.whnf (← current.getType)
      let args := target.getAppArgs
      unless target.isAppOfArity ``Exists 2 do throwError "expected prefix existential"
      let app ← Lean.Meta.mkAppOptM ``Exists.intro #[some args[0]!,some args[1]!,some value]
      let next ← current.apply app
      unless next.length == 1 do throwError "unexpected existential shape"
      current := next.head!
    return [current]

def WriterPrefix (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) : Prop :=
  ∃ zero g preparation initial root geometry pending returned flushed parsed splitValue,
    ops.op16 = ok splitValue ∧ split.val = splitValue.val ∧
    ops.op3 proof = ok (.Ok parsed) ∧ ops.op4 proof = ok (.Ok ()) ∧ ops.op1 = ok zero ∧
    ops.op7 D semantic proof hash obs (Array.repeat 29#usize zero) = ok (preparation,g) ∧
    core.result.Result.Insts.CoreOpsTry.branch preparation = ok (.Continue p) ∧
    ops.op12 .S2 = ok (.Ok initial) ∧
    ops.op5 D proof p root 0#usize hash = ok (.Ok ()) ∧
    ops.op11 p.queries 0#usize split = ok (.Ok geometry) ∧
    ops.op10 initial.weights.deref = ok (.Ok pending) ∧
    ops.op6 proof p initial g obs geometry pending split = ok (.Ok returned) ∧
    ops.op9 returned.2 returned.1.weights.deref = ok flushed ∧
    a.weights.val = flushed.val ∧ a.rhs = returned.1.rhs ∧ a.power = returned.1.power ∧ a.next = returned.1.next

theorem writer_prefix (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ p a, WriterPrefix ops D hash semantic proof split obs p a ∧
      ops.op8 D p a proof pub hash = ok saved := by
  unfold verifier.candidate.tx1 at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have same := core.result.Result.Ok.inj (Result.ok.inj accepted)
    rw [← same]
    refine ⟨_,_,?_,by assumption⟩
    unfold WriterPrefix
    vtop_prefix_witnesses
    repeat' apply And.intro
    all_goals first | assumption | rfl | (aesop (add simp [bne_iff_ne]))

#print axioms writer_prefix
end AspisR1.VTop_Provenance
end
