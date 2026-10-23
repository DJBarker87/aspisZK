import VTop_Provenance
import VTop_Cuts
import Port2_Initial

/-! Inversion of the actual extracted source call sites. No child output is
chosen independently of this accepted stage execution. This does not supply
the missing arithmetic/body interpretations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port2_ReturnedState
open Aeneas Aeneas.Std Result VTop_Stages

/-- Actual TX2 caller cuts in source order, retaining full returned states.
The final View is precisely the one passed to op19 (not an independent read). -/
def FinishPrefix (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (pub proof ck : Slice U8)
    (obs : Option (verifier.Phase → Result Unit))
    (p : verifier.Prepared) (a : verifier.Accumulator) (v : verifier.View) : Prop :=
  ∃ resumed split g root geometry pending returned flushed,
    ops.op18 D ck proof pub .S2 hash = ok (.Ok (p,resumed)) ∧
    ops.op16 = ok split ∧ resumed.next.val = split.val ∧
    ops.op17 29#usize p.gamma = ok g ∧
    ops.op5 D proof p root 1#usize hash = ok (.Ok ()) ∧
    ops.op11 p.queries resumed.next 22#usize = ok (.Ok geometry) ∧
    ops.op10 resumed.weights.deref = ok (.Ok pending) ∧
    ops.op6 proof p resumed g obs geometry pending 22#usize = ok (.Ok returned) ∧
    ops.op9 returned.2 returned.1.weights.deref = ok flushed ∧
    a.weights.val = flushed.val ∧ a.rhs = returned.1.rhs ∧
    a.power = returned.1.power ∧ a.next = returned.1.next ∧
    v.variant = .S2 ∧ v.semantic.val = [] ∧ v.y1.val = [] ∧
    v.folded_root = none ∧ v.query_bytes.val = []

elab "port2_finish_witnesses" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    let find : Lean.Name → Lean.MetaM (Lean.Expr × Lean.Expr) := fun op => do
      for decl in ← Lean.getLCtx do
        if decl.type.isAppOfArity ``Eq 3 then
          let args := decl.type.getAppArgs
          if args[1]!.getAppFn.isConstOf op then
            return (args[1]!,args[2]!.getAppArgs.back!)
      throwError "missing source cut {op}"
    let (_,resumed) ← find ``VTop_Stages.Ops.op18
    let (_,split) ← find ``VTop_Stages.Ops.op16
    let (_,g) ← find ``VTop_Stages.Ops.op17
    let (batch,_) ← find ``VTop_Stages.Ops.op5
    let root := batch.getAppArgs[batch.getAppArgs.size-3]!
    let (_,geometry) ← find ``VTop_Stages.Ops.op11
    let (_,pending) ← find ``VTop_Stages.Ops.op10
    let (_,returned) ← find ``VTop_Stages.Ops.op6
    let (_,flushed) ← find ``VTop_Stages.Ops.op9
    let inner (e : Lean.Expr) := e.getAppArgs.back!
    let a ← Lean.Meta.mkAppM ``Prod.snd #[inner resumed]
    let mut current := goal
    for value in #[a,split,g,root,inner geometry,inner pending,inner returned,flushed] do
      let target ← Lean.Meta.whnf (← current.getType)
      let args := target.getAppArgs
      unless target.isAppOfArity ``Exists 2 do throwError "expected cut existential"
      let app ← Lean.Meta.mkAppOptM ``Exists.intro #[some args[0]!,some args[1]!,some value]
      let next ← current.apply app
      unless next.length == 1 do throwError "unexpected cut existential"
      current := next.head!
    return [current]

theorem finish_prefix (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof ck : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_authenticated ops D pub proof ck hash obs = ok (.Ok ())) :
    ∃ p a v, FinishPrefix ops D hash pub proof ck obs p a v ∧
      ops.op19 v p a obs = ok (.Ok ()) := by
  unfold verifier.candidate.tx2_authenticated verifier.candidate.tx2_common at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    refine ⟨_,_,_,?_,by assumption⟩
    unfold FinishPrefix
    port2_finish_witnesses
    repeat' apply And.intro
    all_goals first | assumption | rfl | (aesop (add simp [bne_iff_ne]))

/-- The source writer's state is the returned query state after the actual
Vec write-back, with its non-weight arithmetic fields preserved. -/
theorem writer_returned (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 ops D semantic pub proof split hash obs = ok (.Ok saved)) :
    ∃ p a initial geometry pending returned flushed g,
      ops.op12 .S2 = ok (.Ok initial) ∧
      ops.op11 p.queries 0#usize split = ok (.Ok geometry) ∧
      ops.op10 initial.weights.deref = ok (.Ok pending) ∧
      ops.op6 proof p initial g obs geometry pending split = ok (.Ok returned) ∧
      ops.op9 returned.2 returned.1.weights.deref = ok flushed ∧
      a.weights.val = flushed.val ∧ a.rhs = returned.1.rhs ∧
      a.power = returned.1.power ∧ a.next = returned.1.next ∧
      ops.op8 D p a proof pub hash = ok saved := by
  obtain ⟨p,a,reached,wrote⟩ := VTop_Provenance.writer_prefix ops D hash semantic pub proof split obs saved accepted
  obtain ⟨zero,g,preparation,initial,root,geometry,pending,returned,flushed,parsed,splitValue,
    hs,hsv,hparse,hscan,hzero,hprep,hbranch,hinit,hbatch,hgeom,hpending,hquery,hflush,
    hweights,hrhs,hpower,hnext⟩ := reached
  exact ⟨p,a,initial,geometry,pending,returned,flushed,g,hinit,hgeom,hpending,hquery,
    hflush,hweights,hrhs,hpower,hnext,wrote⟩

#print axioms finish_prefix
#print axioms writer_returned
end AspisR1.Port2_ReturnedState
end
