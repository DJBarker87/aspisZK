import NNG_SourcePayload136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SourceCircleGuard136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_Projection136 NNG_Observed136 NNG_OccurrenceLaws136 NNG_SourceStep136 NNG_LawStep136

theorem guard (VL : RSL.VLib) {H W : Type} (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H) (b : Bool)
    (boolEq : b = decide (p.point z0 = p.point z1))
    (h : Laws VL p c s events env (NNG_TreeSuffixes.f_circleGuard c s alpha claims extra state z0 before t3 z1 b)) :
    NNG_Canonical136.circleGuard VL (args p s) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_circleGuard c s alpha claims extra state z0 before t3 z1 b)) := by
  unfold NNG_Canonical136.circleGuard
  rw [←boolEq]
  cases b with
  | false =>
    rw [RSL.RE.check_false,RSL.RE.seq_pure]
    have hnext : Laws VL p c s events env (NNG_TreeSuffixes.f_r10 c s alpha claims extra state z0 before t3 z1) := h
    exact NNG_SourcePayload136.source VL p c s events env alpha claims extra before state z0 z1 t3 hnext
  | true =>
    rw [RSL.RE.check_true,RSL.RE.seq_throw]
    change (⟨.ret (.error (p.error r1_wire.Error.EqualCirclePoints)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) =
      ⟨.ret (.error VL.wEqualCirclePoints),[]⟩
    rw [p.equalError]
#print axioms guard

theorem source (VL : RSL.VLib) {H W : Type} (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H)
    (h : Laws VL p c s events env (NNG_TreeSuffixes.f_b1 c s alpha claims extra state z0 before t3 z1)) :
    NNG_Canonical136.circleGuard VL (args p s) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_b1 c s alpha claims extra state z0 before t3 z1)) := by
  have comparison : c.c2 z0 z1 = .ok (decide (z0=z1)) := by rw [h.pointEq]; rfl
  have hnext : Laws VL p c s events env
      (NNG_TreeSuffixes.f_circleGuard c s alpha claims extra state z0 before t3 z1 (decide (z0=z1))) := by
    apply same_trace VL p c s events env _ _ h
    unfold NNG_TreeSuffixes.f_b1
    rw [comparison]
    rfl
  unfold NNG_TreeSuffixes.f_b1
  rw [comparison]
  exact guard VL p c s events env alpha claims extra before state z0 z1 t3 _ (point_eq p z0 z1) hnext
#print axioms source
end AspisR1.NNG_SourceCircleGuard136
