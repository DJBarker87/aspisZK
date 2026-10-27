import XRk_ScratchProjection
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_RejectedScratch
theorem rejected_scratch {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (old scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (error : verifier.Error)
    (h : verifier.Prepared.new D sem v hash old = ok (.Err error,scratch)) :
    scratch = old ∨ ∃ gamma, weights.powers 29#usize gamma = ok scratch := by
  unfold verifier.Prepared.new at h
  simp only [r1_wire.SemanticTranscript.impl.state,bind_tc_ok] at h
  obtain ⟨start,_,h⟩ := bind_success _ _ _ h
  obtain ⟨gamma,t1,_,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨inactiveBytes,_,h⟩ := bind_success _ _ _ h
  try simp only [lift,bind_tc_ok] at h
  obtain ⟨kappa,t2,_,h⟩ := pair_bind_success _ _ _ h
  obtain ⟨alpha0,t3,_,h⟩ := pair_bind_success _ _ _ h
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
      exact Or.inl (congrArg Prod.snd (Result.ok.inj h)).symm
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_success _ _ _ h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨rho,last,_,h⟩ := pair_bind_success _ _ _ h
      obtain ⟨computed,hpowers,h⟩ := bind_success _ _ _ h
      obtain ⟨ret,_,h⟩ := bind_success _ _ _ h
      cases ret with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        have hs := congrArg Prod.snd (Result.ok.inj h)
        change computed = scratch at hs
        exact Or.inr ⟨gamma,hpowers.trans (congrArg Result.ok hs)⟩
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
  · obtain ⟨zero,_,h⟩ := bind_success _ _ _ h
    obtain ⟨ret,afterQueries,_,h⟩ := pair_bind_success _ _ _ h
    cases ret with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at h
      exact Or.inl (congrArg Prod.snd (Result.ok.inj h)).symm
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_success _ _ _ h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨rho,last,_,h⟩ := pair_bind_success _ _ _ h
      obtain ⟨computed,hpowers,h⟩ := bind_success _ _ _ h
      obtain ⟨ret,_,h⟩ := bind_success _ _ _ h
      cases ret with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at h
        have hs := congrArg Prod.snd (Result.ok.inj h)
        change computed = scratch at hs
        exact Or.inr ⟨gamma,hpowers.trans (congrArg Result.ok hs)⟩
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h

#print axioms rejected_scratch
end XRk_RejectedScratch
