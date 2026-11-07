import NNG_DSourceHigh
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceLow
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Array136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript H)
    (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_a c s running terminal alpha t1 claims)) :
    NNG_Canonical136.mask VL a (p.q running) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_a c s running terminal alpha t1 claims)) := by
  have selected : c.c0 16#usize (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 s.digest) claims = .ok (NNG_FromFnValues136.low claims) := by
    rw [h.fromFn]
    exact NNG_FromFnValues136.first s.digest claims
  have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_a1 c s running terminal alpha t1 claims (NNG_FromFnValues136.low claims)) := by
    apply same_trace VL a p c s events env _ _ h
    unfold NNG_TreeSuffixes.f_a
    dsimp only
    rw [selected]
    rfl
  unfold NNG_TreeSuffixes.f_a
  dsimp only
  rw [selected]
  exact NNG_DSourceHigh.source VL a p c s events env running terminal alpha claims t1 runningDom hn
#print axioms source
end AspisR1.NNG_DSourceLow
