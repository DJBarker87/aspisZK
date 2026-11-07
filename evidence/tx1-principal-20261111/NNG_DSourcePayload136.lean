import NNG_DSourceRoot136
import NNG_DLawStep136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourcePayload136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type} (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r10 c s alpha claims extra state z0 before t3 z1)) :
    NNG_Canonical136.payload2 VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_r10 c s alpha claims extra state z0 before t3 z1)) := by
  let head := invoke "payload2" (s.prefixValue,2#u8) (c.c12 s.prefixValue 2#u8)
  let k : core.result.Result (Slice U8) r1_wire.Error → Code (Output H) := fun r10 => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r10
    match cf with
    | core.ops.control_flow.ControlFlow.Continue bytes =>
      NNG_TreeSuffixes.f_r11 c s alpha claims extra state z0 before t3 z1 bytes
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r10 c s alpha claims extra state z0 before t3 z1 =
      NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "payload2" (s.prefixValue,2#u8) (c.c12 s.prefixValue 2#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (RSL.RE.ofExcept (VL.payload a.prefix_ 2)) env
      (observation (payloadReply p) (events env) head) := by
    rw [←h.payload2 ent]
    exact call_actual (payloadReply p) events "payload2" (s.prefixValue,2#u8) (c.c12 s.prefixValue 2#u8) env
  unfold NNG_Canonical136.payload2 RSL.RE.bind
  refine bind_sound head k (payloadReply p) (output p) (events env) env _ _ headLaw ?_
  intro r returned
  cases r with
  | Ok bytes =>
    change NNG_Canonical136.root32 VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) (p.bytes bytes) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_r11 c s alpha claims extra state z0 before t3 z1 bytes))
    exact NNG_DSourceRoot136.root32 p c s a h.inputs events env alpha claims extra before state z0 z1 t3 bytes
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) =
      ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourcePayload136
