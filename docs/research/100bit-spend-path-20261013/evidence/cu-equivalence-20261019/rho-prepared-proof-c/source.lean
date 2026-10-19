import AspisR1RhoPrepared.Funs
import CuSavingsRhoPreparedScalar

/-! The complete actual preparation caller derives its stored rho invariant
from the actual source scalar_k call. All other common computations remain
arbitrary and may fail/diverge. No child-success or canonicality premise is
supplied to the theorem. Both source fold branches and source errors remain.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoPrepared
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks]

theorem source_success {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch finalScratch : Array aspis_core.field.WideExact 29#usize)
    (out : verifier.Prepared)
    (h : gamma_new.Prepared.gamma_new_new D sem v hash scratch = .ok (.Ok out,finalScratch)) :
    CuSavingsRhoPowerTail.Canonical out.rho ∧
      ∃ before after row payload sourceRho,
        AspisR1CuRho.transcript.Transcript.scalar_k D before row payload = .ok (sourceRho,after) ∧
        fromRhoSource sourceRho=out.rho ∧ out.state=after.state := by
  unfold gamma_new.Prepared.gamma_new_new at h
  obtain ⟨initial,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨t,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨gamma,t1⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨bytes,_,h⟩ := bind_ok _ _ _ h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨⟨kappa,t2⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨alpha0,t3⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨folds,_,h⟩ := bind_ok _ _ _ h
  split at h
  · obtain ⟨capacity,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨root,_,h⟩ := bind_ok _ _ _ h
    simp only [lift,bind_tc_ok] at h
    obtain ⟨bytes1,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨bytes2,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨⟨alpha1,t4⟩,_,h⟩ := bind_ok _ _ _ h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨⟨queries,t5⟩,_,h⟩ := bind_ok _ _ _ h
    try simp only [uncurry_apply_pair] at h
    cases queries with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_ok _ _ _ h
      simp only [lift,bind_tc_ok] at h
      obtain ⟨⟨rho,t6⟩,hs,h⟩ := bind_ok _ _ _ h
      try simp only [uncurry_apply_pair] at h
      have hsource := CuSavingsRhoPreparedScalar.scalar_success D t5 t6 row _ rho hs
      obtain ⟨powers,_,h⟩ := bind_ok _ _ _ h
      obtain ⟨claim,_,h⟩ := bind_ok _ _ _ h
      cases claim with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have heq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
        have hrho : rho=out.rho := congrArg verifier.Prepared.rho heq
        have hstate := congrArg verifier.Prepared.state heq
        obtain ⟨source,hactual,hfrom⟩ := hsource.2
        refine ⟨?_,t5,t6,row,_,source,hactual,?_,?_⟩
        · simpa only [hrho] using hsource.1
        · exact hfrom.trans hrho
        · exact hstate.symm
  · obtain ⟨⟨queries,t4⟩,_,h⟩ := bind_ok _ _ _ h
    try simp only [uncurry_apply_pair] at h
    cases queries with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_ok _ _ _ h
      simp only [lift,bind_tc_ok] at h
      obtain ⟨⟨rho,t5⟩,hs,h⟩ := bind_ok _ _ _ h
      try simp only [uncurry_apply_pair] at h
      have hsource := CuSavingsRhoPreparedScalar.scalar_success D t4 t5 row _ rho hs
      obtain ⟨powers,_,h⟩ := bind_ok _ _ _ h
      obtain ⟨claim,_,h⟩ := bind_ok _ _ _ h
      cases claim with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have heq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
        have hrho : rho=out.rho := congrArg verifier.Prepared.rho heq
        have hstate := congrArg verifier.Prepared.state heq
        obtain ⟨source,hactual,hfrom⟩ := hsource.2
        refine ⟨?_,t4,t5,row,_,source,hactual,?_,?_⟩
        · simpa only [hrho] using hsource.1
        · exact hfrom.trans hrho
        · exact hstate.symm

#print axioms source_success
end AspisR1.CuSavingsRhoPrepared
