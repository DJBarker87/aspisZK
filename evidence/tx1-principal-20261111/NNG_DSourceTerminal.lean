import NNG_DSourceMark3
import NNG_DPublicMap136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceTerminal
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript H)
    (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r2 c s running alpha t1 claims)) :
    NNG_Canonical136.terminal VL a (p.q running) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r2 c s running alpha t1 claims)) := by
  let first := invoke "terminal" (s.publicValue,claims,alpha,s.challenges) (c.c7 s.publicValue claims alpha s.challenges)
  let mapped : core.result.Result Q aspis_core.state_only_prefix.r0.Error → Code (core.result.Result Q r1_wire.Error) :=
    fun r => liftM (c.c1 (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError s.digest) r ())
  let head := NMT_CallTree.bind first mapped
  let k : core.result.Result Q r1_wire.Error → Code (Output H) := fun r3 => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf with
    | core.ops.control_flow.ControlFlow.Continue terminal =>
      NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r2 c s running alpha t1 claims = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "terminal" (s.publicValue,claims,alpha,s.challenges)
      (c.c7 s.publicValue claims alpha s.challenges) ∈ (run (NMT_CallTree.bind head k)).2 := by
    exact entered _ _ _ _
  have firstLaw : (VL.terminalQm31.run (a.public_,p.claims claims,p.alpha alpha,VL.origChallenges a.challenges)) env
      (observation (terminalReply p) (events env) first) := by
    rw [←h.terminal claims alpha ent]
    exact call_actual (terminalReply p) events "terminal" (s.publicValue,claims,alpha,s.challenges)
      (c.c7 s.publicValue claims alpha s.challenges) env
  have headLaw : (RSL.RE.mapErr (fun _ => VL.wPublic)
      (VL.terminalQm31.run (a.public_,p.claims claims,p.alpha alpha,VL.origChallenges a.challenges))) env
      (observation (NNG_DPublicMap136.qReply p) (events env) head) := by
    unfold RSL.RE.mapErr RSL.Spec.map
    refine bind_sound first mapped (terminalReply p) (NNG_DPublicMap136.qReply p) (events env) env _ _ firstLaw ?_
    intro r returned
    change observation (NNG_DPublicMap136.qReply p) (events env) (mapped r) = _
    apply silent_result
    change NNG_EmittedCallGraph.resultMap (NNG_DPublicMap136.qReply p)
      (c.c1 (r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError s.digest) r ()) = _
    rw [h.mapErr]
    exact NNG_DPublicMap136.projected p s.digest r
  unfold NNG_Canonical136.terminal RSL.RE.bind
  refine bind_sound head k (NNG_DPublicMap136.qReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  cases reply with
  | Ok terminal =>
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.mask VL a (p.q running) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims))
    exact NNG_DSourceMark3.source VL a p c s events env running terminal alpha claims t1 runningDom hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceTerminal
