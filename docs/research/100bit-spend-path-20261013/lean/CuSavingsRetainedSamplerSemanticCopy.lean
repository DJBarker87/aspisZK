import AspisR1RhoPrepared.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSamplerSemanticCopy
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ x,m=.ok x ∧ k x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩
variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks]
theorem source_success {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch finalScratch : Array aspis_core.field.WideExact 29#usize)
    (out : verifier.Prepared)
    (h : gamma_new.Prepared.gamma_new_new D sem v hash scratch=.ok (.Ok out,finalScratch)) :
    out.semantic_alpha=sem.alpha := by
  unfold gamma_new.Prepared.gamma_new_new at h
  obtain ⟨initial,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨t,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨gamma,t1⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨bytes,_,h⟩ := bind_ok _ _ _ h
  try simp only [lift,bind_tc_ok] at h
  obtain ⟨⟨kappa,t2⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨alpha0,t3⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨folds,_,h⟩ := bind_ok _ _ _ h
  split at h
  · obtain ⟨capacity,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨root,_,h⟩ := bind_ok _ _ _ h
    try simp only [lift,bind_tc_ok] at h
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
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨⟨rho,t6⟩,hs,h⟩ := bind_ok _ _ _ h
      try simp only [uncurry_apply_pair] at h

      obtain ⟨powers,_,h⟩ := bind_ok _ _ _ h
      obtain ⟨claim,_,h⟩ := bind_ok _ _ _ h
      cases claim with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have heq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
        exact (congrArg verifier.Prepared.semantic_alpha heq).symm

  · obtain ⟨⟨queries,t4⟩,_,h⟩ := bind_ok _ _ _ h
    try simp only [uncurry_apply_pair] at h
    cases queries with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,_,h⟩ := bind_ok _ _ _ h
      try simp only [lift,bind_tc_ok] at h
      obtain ⟨⟨rho,t5⟩,hs,h⟩ := bind_ok _ _ _ h
      try simp only [uncurry_apply_pair] at h

      obtain ⟨powers,_,h⟩ := bind_ok _ _ _ h
      obtain ⟨claim,_,h⟩ := bind_ok _ _ _ h
      cases claim with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have heq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
        exact (congrArg verifier.Prepared.semantic_alpha heq).symm

#print axioms source_success
end AspisR1.CuSavingsRetainedSamplerSemanticCopy
