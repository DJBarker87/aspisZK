import NNG_DSourceMark4
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceTerminalGuard
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem guard (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running masked : VL.QM31) (alpha : Alpha) (claims : Claims) (extra : K29)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord) (b : Bool)
    (boolEq : b = decide (running ≠ masked))
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_terminalGuard c s alpha t1 claims extra b (.Ok rec25))) :
    NNG_Canonical136.terminalGuard VL a running masked (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_terminalGuard c s alpha t1 claims extra b (.Ok rec25))) := by
  unfold NNG_Canonical136.terminalGuard
  rw [←boolEq]
  cases b with
  | false =>
    rw [RSL.RE.check_false,RSL.RE.seq_pure]
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark4 c s alpha t1 claims extra (.Ok rec25)) := h
    exact NNG_DSourceMark4.source VL a p c s events env alpha claims extra t1 rec25 saved hn
  | true =>
    rw [RSL.RE.check_true,RSL.RE.seq_throw]
    change (⟨.ret (.error (p.error r1_wire.Error.Terminal)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) =
      ⟨.ret (.error VL.wTerminal),[]⟩
    rw [p.terminalError]
#print axioms guard

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running masked : Q) (alpha : Alpha) (claims : Claims) (extra : K29)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord)
    (runningDom : p.qDom running) (maskedDom : p.qDom masked)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_b c s running masked alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.terminalGuard VL a (p.q running) (p.q masked) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_b c s running masked alpha t1 claims extra (.Ok rec25))) := by
  have comparison : core.cmp.PartialEq.ne.trait_default
      (aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 c.c3) running masked = .ok (decide (running≠masked)) := by
    rw [h.qeq]
    exact NNG_Equality136.terminal_guard running masked
  have hn : Laws VL a p c s events env
      (NNG_TreeSuffixes.f_terminalGuard c s alpha t1 claims extra (decide (running≠masked)) (.Ok rec25)) := by
    apply same_trace VL a p c s events env _ _ h
    unfold NNG_TreeSuffixes.f_b
    rw [comparison]
    rfl
  unfold NNG_TreeSuffixes.f_b
  rw [comparison]
  exact guard VL a p c s events env (p.q running) (p.q masked) alpha claims extra t1 rec25 _
    (q_ne p running masked runningDom maskedDom) saved hn
#print axioms source
end AspisR1.NNG_DSourceTerminalGuard
