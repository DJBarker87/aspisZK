import CurrentPreparedScratchReachability
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PreparedScratchTransport
open PreparedScratchReachability

private theorem pair_let {A B C : Type} (a : A) (b : B) (f : A → B → C) :
    (let (x,y) := (a,b); f x y) = f a b := rfl

/-- The cached gamma-power claim implements the same relation as the retained
claim interface, on the very array returned by current powers. This is a named
arithmetic/source obligation, not an axiom or a successful-call premise. -/
def ClaimsAgree (B : PreparedScratchModel.Boundaries) : Prop :=
  ∀ {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y : Slice U8) (inactive gamma kappa : Wide) (g : Array Wide 29#usize),
    B.powers 29#usize gamma = ok g →
    B.claim D sem y inactive g kappa =
      B.sampling.claim D sem y inactive gamma kappa

/-- Reuse the retained sampler/caller results against the current Prepared
body. All child success witnesses come from the checked new-body trace;
only the cached/uncached claim correspondence remains an explicit premise. -/
theorem current_success_reuses_retained_prepare {H : Type}
    (B : PreparedScratchModel.Boundaries) (agree : ClaimsAgree B)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (out : verifier.Prepared)
    (scratchIn scratch : Array Wide 29#usize)
    (h : PreparedScratchModel.prepare B D sem v hash scratchIn = ok (.Ok out, scratch)) :
    PreparedModel.prepare B.sampling D sem v hash = ok (.Ok out) := by
  obtain ⟨start, t1, t2, t3, inactiveBytes, gamma, kappa, alpha0,
    hseed, hgamma, hbytes, hkappa, halpha0, tail⟩ :=
      PreparedScratchReachability.prepare_success B D sem v hash out scratch scratchIn h
  have add_exact {ty : UScalarTy} (a b c : UScalar ty)
      (hc : c.val = a.val + b.val) : a + b = ok c := by
    obtain ⟨z, hz, _⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := a) (y := b) (by scalar_tac))
    have he : z = c := by scalar_tac
    simpa only [he] using hz
  have hcap : 32#usize + 224#usize = ok 256#usize := add_exact _ _ _ (by scalar_tac)
  have hsingle : 30#u8 + 1#u8 = ok 31#u8 := add_exact _ _ _ (by scalar_tac)
  have hdouble : 31#u8 + 1#u8 = ok 32#u8 := add_exact _ _ _ (by scalar_tac)
  have hne : ¬ (1#usize = 2#usize) := by decide
  cases tail with
  | single hfolds tail =>
    obtain ⟨queries, afterQueries, last, rho, claim, hqueries, hrho,
      hpowers, hclaim, hout⟩ := tail
    have hc : B.sampling.claim D sem v.y1 v.inactive gamma kappa = ok (.Ok claim) := by
      rw [← agree D sem v.y1 v.inactive gamma kappa scratch hpowers]
      exact hclaim
    have hr : PreparedModel.scalar_k B.sampling D afterQueries 31#u8 emptyPayload = ok (rho, last) := by
      simpa only [if_pos rfl, ite_true] using hrho
    subst out
    unfold PreparedModel.prepare
    simp only [r1_wire.SemanticTranscript.impl.state, hseed, hgamma, hbytes,
      lift, hkappa, halpha0, hfolds, bind_tc_ok, if_neg hne, hqueries,
      core.result.Result.Insts.CoreOpsTry.branch, hsingle, hr, hc, output,
      emptyPayload, pair_let, ite_true, ite_false]
  | double hfolds root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1 tail =>
    obtain ⟨queries, afterQueries, last, rho, claim, hqueries, hrho,
      hpowers, hclaim, hout⟩ := tail
    have hc : B.sampling.claim D sem v.y1 v.inactive gamma kappa = ok (.Ok claim) := by
      rw [← agree D sem v.y1 v.inactive gamma kappa scratch hpowers]
      exact hclaim
    have hr : PreparedModel.scalar_k B.sampling D afterQueries 32#u8 emptyPayload = ok (rho, last) := by
      simpa only [if_neg (show ¬ (31#u8 = 30#u8) by decide)] using hrho
    subst out
    unfold PreparedModel.prepare
    simp only [r1_wire.SemanticTranscript.impl.state, hseed, hgamma, hbytes,
      lift, hkappa, halpha0, hfolds, bind_tc_ok, if_pos rfl, hcap, hroot,
      hbytes1, hbytes2, halpha1, hqueries, core.result.Result.Insts.CoreOpsTry.branch,
      hdouble, hr, hc, output, emptyPayload, pair_let, ite_true, ite_false]

#print axioms current_success_reuses_retained_prepare
end AspisR1PublicPreparation.PreparedScratchTransport
