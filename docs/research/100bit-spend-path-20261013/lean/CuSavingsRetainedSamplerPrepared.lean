import CuSavingsRetainedSamplerBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSamplerPrepared
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail CuSavingsRetainedSamplerBinding
variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]
private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ x,m=.ok x ∧ k x=.ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩
theorem source_success (common : PreparedCommon) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch finalScratch : Array E 29#usize) (out : verifier.Prepared)
    (h : letI : PreparedCommon := binding common
         gamma_new.Prepared.gamma_new_new D sem v hash scratch=.ok (.Ok out,finalScratch)) :
    CuSavingsCanonicalDotsSources.SourceValue (input out.gamma) ∧ out.variant=v.variant ∧
      ∃ a0 a1,out.alpha=Array.make 2#usize [a0,a1] ∧ CuSavingsLibraOrigins.Alpha (libra a0) ∧
        (CuSavingsLibraOrigins.Alpha (libra a1) ∨
          (transport.Variant.folds v.variant≠.ok 2#usize ∧ a1=aspis_core.field.WideExact.ZERO)) ∧
        ∃ source,AspisR1CanonicalInputs.weights.powers 29#usize (input out.gamma)=.ok source ∧
          finalScratch=table source := by
  letI : PreparedCommon := binding common
  unfold gamma_new.Prepared.gamma_new_new at h
  obtain ⟨initial,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨t,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨⟨gamma,t1⟩,hgammaSample,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨bytes,_,h⟩ := bind_ok _ _ _ h
  try simp only [lift,bind_tc_ok] at h
  obtain ⟨⟨kappa,t2⟩,_,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨alpha0,t3⟩,ha0,h⟩ := bind_ok _ _ _ h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨folds,hfolds,h⟩ := bind_ok _ _ _ h
  change scalar D t 27#u8 v.y1 true=.ok (gamma,t1) at hgammaSample
  change scalar D t2 29#u8 v.round0 false=.ok (alpha0,t3) at ha0
  have hgOrigin := (scalar_origins D t t1 27#u8 v.y1 true gamma hgammaSample).1
  have ha0Origin := (scalar_origins D t2 t3 29#u8 v.round0 false alpha0 ha0).2 rfl
  split at h
  · obtain ⟨capacity,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨root,_,h⟩ := bind_ok _ _ _ h
    try simp only [lift,bind_tc_ok] at h
    obtain ⟨bytes1,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨bytes2,_,h⟩ := bind_ok _ _ _ h
    obtain ⟨⟨alpha1,t4⟩,ha1,h⟩ := bind_ok _ _ _ h
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
      have ha1Origin := (scalar_origins D t3 t4 30#u8 _ false alpha1 ha1).2 rfl
      obtain ⟨powerTable,hpowers,h⟩ := bind_ok _ _ _ h
      obtain ⟨claim,_,h⟩ := bind_ok _ _ _ h
      cases claim with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have heq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
        have hg := congrArg verifier.Prepared.gamma heq
        change gamma=out.gamma at hg
        have halpha := congrArg verifier.Prepared.alpha heq
        have hvariant := congrArg verifier.Prepared.variant heq
        have hfinal := congrArg Prod.snd (Result.ok.inj h)
        change powers 29#usize gamma=.ok powerTable at hpowers
        obtain ⟨source,hsource,htable⟩ := powers_source 29#usize gamma powerTable hpowers
        refine ⟨?_,hvariant.symm,alpha0,alpha1,halpha.symm,ha0Origin,Or.inl ha1Origin,source,?_,?_⟩
        · simpa only [hg] using hgOrigin
        · simpa only [hg] using hsource
        · exact hfinal.symm.trans htable

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

      obtain ⟨powerTable,hpowers,h⟩ := bind_ok _ _ _ h
      obtain ⟨claim,_,h⟩ := bind_ok _ _ _ h
      cases claim with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        cases h
      | Ok claim =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        have heq := core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
        have hg := congrArg verifier.Prepared.gamma heq
        change gamma=out.gamma at hg
        have halpha := congrArg verifier.Prepared.alpha heq
        have hvariant := congrArg verifier.Prepared.variant heq
        have hfinal := congrArg Prod.snd (Result.ok.inj h)
        change powers 29#usize gamma=.ok powerTable at hpowers
        obtain ⟨source,hsource,htable⟩ := powers_source 29#usize gamma powerTable hpowers
        refine ⟨?_,hvariant.symm,alpha0,aspis_core.field.WideExact.ZERO,halpha.symm,ha0Origin,
          Or.inr ⟨?_,rfl⟩,source,?_,?_⟩
        · simpa only [hg] using hgOrigin
        · intro htwo
          have he : folds=2#usize := Result.ok.inj (hfolds.symm.trans htwo)
          contradiction
        · simpa only [hg] using hsource
        · exact hfinal.symm.trans htable

#print axioms source_success
end AspisR1.CuSavingsRetainedSamplerPrepared
