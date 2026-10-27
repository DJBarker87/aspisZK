import XSe_ScalarKCanonical
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRn_Join_Release XRk_ResultTools
namespace XSe_PreparedRho
/- Accepted-result projection from the actual emitted Prepared.new. This is
   one local component, not the full source/reference/effects association. -/
theorem source (low : XRz_HybridSampler.Low) {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (old scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (out : verifier.Prepared)
    (h : XRz_HybridPrepared.prepared low D sem v hash old = ok (.Ok out,scratch)) :
    XRp_PowersQAdd.CanonicalQ out.rho := by
  unfold XRz_HybridPrepared.prepared at h
  simp only [r1_wire.SemanticTranscript.impl.state,bind_tc_ok] at h
  obtain ⟨start,hstart,h⟩ := bind_success _ _ _ h
  obtain ⟨gamma,t1,hgamma,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨inactiveBytes,hinactive,h⟩ := bind_success _ _ _ h
  try simp only [lift,bind_tc_ok] at h
  obtain ⟨kappa,t2,hkappa,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨alpha0,t3,halpha,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨folds,_,h⟩ := bind_success _ _ _ h
  split at h
  · obtain ⟨capacity,_,h⟩ := bind_success _ _ _ h
    obtain ⟨root,_,h⟩ := bind_success _ _ _ h
    try simp only [lift,bind_tc_ok] at h
    obtain ⟨bytes1,_,h⟩ := bind_success _ _ _ h
    obtain ⟨bytes2,_,h⟩ := bind_success _ _ _ h
    obtain ⟨alpha1,afterAlpha,_,h⟩ := pair_bind_success _ _ _ h
    obtain ⟨ret,afterQueries,_,h⟩ := pair_bind_success _ _ _ h
    cases ret with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_success _ _ _ h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨rho,last,hrho,h⟩ := pair_bind_success _ _ _ h
      obtain ⟨computed,hpowers,h⟩ := bind_success _ _ _ h
      obtain ⟨ret,_,h⟩ := bind_success _ _ _ h
      cases ret with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have same := Result.ok.inj h
        have hp := core.result.Result.Ok.inj (congrArg Prod.fst same)
        have sameRho := congrArg verifier.Prepared.rho hp
        change rho=out.rho at sameRho
        rw [←sameRho]
        exact XSe_ScalarKCanonical.source D _ _ _ _ rho hrho
  · obtain ⟨zero,_,h⟩ := bind_success _ _ _ h
    obtain ⟨ret,afterQueries,_,h⟩ := pair_bind_success _ _ _ h
    cases ret with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_success _ _ _ h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨rho,last,hrho,h⟩ := pair_bind_success _ _ _ h
      obtain ⟨computed,hpowers,h⟩ := bind_success _ _ _ h
      obtain ⟨ret,_,h⟩ := bind_success _ _ _ h
      cases ret with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have same := Result.ok.inj h
        have hp := core.result.Result.Ok.inj (congrArg Prod.fst same)
        have sameRho := congrArg verifier.Prepared.rho hp
        change rho=out.rho at sameRho
        rw [←sameRho]
        exact XSe_ScalarKCanonical.source D _ _ _ _ rho hrho
#print axioms source
end XSe_PreparedRho
