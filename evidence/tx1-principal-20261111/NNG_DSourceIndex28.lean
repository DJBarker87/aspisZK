import NNG_DSourceAddExtra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceIndex28
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Array136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running partialValue : Q) (alpha : Alpha) (claims : Claims) (extra : K29)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord) (runningDom : p.qDom running)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_q3 c s running partialValue alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.addExtra VL a (p.q running) (p.q partialValue) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_q3 c s running partialValue alpha t1 claims extra (.Ok rec25))) := by
  have selected : Array.index_usize extra 28#usize = .ok (get extra 28#usize (by decide)) := NNG_Array136.index extra 28#usize (by decide)
  have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_masked_terminal c s running partialValue
      (get extra 28#usize (by decide)) alpha t1 claims extra (.Ok rec25)) := by
    apply same_trace VL a p c s events env _ _ h
    unfold NNG_TreeSuffixes.f_q3
    rw [selected]
    rfl
  unfold NNG_TreeSuffixes.f_q3
  rw [selected]
  exact NNG_DSourceAddExtra.source VL a p c s events env running partialValue alpha claims extra t1 rec25 runningDom saved hn
#print axioms source
end AspisR1.NNG_DSourceIndex28
