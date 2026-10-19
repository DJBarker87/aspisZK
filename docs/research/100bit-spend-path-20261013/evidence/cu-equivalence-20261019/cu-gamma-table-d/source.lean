import AspisR1CuGamma.Funs

/-! Actual complete new preparation success supplies its retained power table
at its returned gamma. No claim-equivalence or decoder-success premise is used;
the old/new claim boundaries remain separate and universally quantified. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsGammaTable
open Aeneas Aeneas.Std Result AspisR1CuGamma
abbrev E := aspis_core.field.WideExact
abbrev Table := Array E 29#usize
abbrev Prepared := verifier.Prepared
abbrev Err := verifier.Error

private theorem step {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x) = .ok out) : ∃ x, m = .ok x ∧ k x = .ok out := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

variable [Boundaries]

def finishWithTable (gamma : E)
    (claim : Table → Result (core.result.Result E Err)) (make : E → Prepared) :
    Result ((core.result.Result Prepared Err) × Table) := do
  let g ← weights.powers 29#usize gamma
  let r ← claim g
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue value => .ok (.Ok (make value),g)
  | .Break residual =>
    let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Prepared (core.convert.FromSame Err) residual
    .ok (r1,g)

theorem finish_table (gamma : E)
    (claim : Table → Result (core.result.Result E Err)) (make : E → Prepared)
    (hgamma : ∀ value, (make value).gamma = gamma)
    (p : Prepared) (gout : Table)
    (h : finishWithTable gamma claim make = .ok (.Ok p,gout)) :
    weights.powers 29#usize p.gamma = .ok gout := by
  unfold finishWithTable at h
  obtain ⟨g,hpow,h⟩ := step _ _ _ h
  obtain ⟨r,hclaim,h⟩ := step _ _ _ h
  cases r with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    have heq := Result.ok.inj h
    have hp : make value = p := core.result.Result.Ok.inj (congrArg Prod.fst heq)
    have hg : g = gout := congrArg Prod.snd heq
    rw [←hp,hgamma,←hg]
    exact hpow

theorem source_success {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (initial : Table) (p : Prepared) (gout : Table)
    (h : gamma_new.Prepared.gamma_new_new D sem v hash initial = .ok (.Ok p,gout)) :
    weights.powers 29#usize p.gamma = .ok gout := by
  unfold gamma_new.Prepared.gamma_new_new at h
  obtain ⟨state,hstate,h⟩ := step _ _ _ h
  obtain ⟨t,ht,h⟩ := step _ _ _ h
  obtain ⟨pair,hscalar,h⟩ := step _ _ _ h
  rcases pair with ⟨gamma,t1⟩
  simp only [uncurry_apply_pair] at h
  obtain ⟨inactiveBytes,hbytes,h⟩ := step _ _ _ h
  simp only [lift,bind_tc_ok] at h
  obtain ⟨pair,hkappa,h⟩ := step _ _ _ h
  rcases pair with ⟨kappa,t2⟩
  simp only [uncurry_apply_pair] at h
  obtain ⟨pair,halpha,h⟩ := step _ _ _ h
  rcases pair with ⟨alpha0,t3⟩
  simp only [uncurry_apply_pair] at h
  obtain ⟨folds,hfolds,h⟩ := step _ _ _ h
  split at h
  · obtain ⟨capacity,hcap,h⟩ := step _ _ _ h
    obtain ⟨root,hroot,h⟩ := step _ _ _ h
    obtain ⟨bytes1,hext1,h⟩ := step _ _ _ h
    obtain ⟨bytes2,hext2,h⟩ := step _ _ _ h
    obtain ⟨pair,halpha1,h⟩ := step _ _ _ h
    rcases pair with ⟨alpha1,t4⟩
    simp only [uncurry_apply_pair] at h
    obtain ⟨pair,hqueries,h⟩ := step _ _ _ h
    rcases pair with ⟨r,t5⟩
    simp only [uncurry_apply_pair] at h
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,hrow,h⟩ := step _ _ _ h
      obtain ⟨pair,hrho,h⟩ := step _ _ _ h
      rcases pair with ⟨rho,t6⟩
      simp only [uncurry_apply_pair] at h
      exact finish_table gamma (fun g => gamma_new.prepared_claim D sem v.y1 v.inactive g kappa)
        (fun claim => {
          variant := v.variant
          roots := sem.roots
          gamma := gamma
          kappa := kappa
          alpha := Array.make 2#usize [alpha0,alpha1]
          rho := rho
          queries := queries
          semantic_alpha := sem.alpha
          z := sem.z
          claim := claim
          state := t6.state }) (fun _ => rfl) p gout h
  · obtain ⟨pair,hqueries,h⟩ := step _ _ _ h
    rcases pair with ⟨r,t4⟩
    simp only [uncurry_apply_pair] at h
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok queries =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨row,hrow,h⟩ := step _ _ _ h
      obtain ⟨pair,hrho,h⟩ := step _ _ _ h
      rcases pair with ⟨rho,t5⟩
      simp only [uncurry_apply_pair] at h
      exact finish_table gamma (fun g => gamma_new.prepared_claim D sem v.y1 v.inactive g kappa)
        (fun claim => {
          variant := v.variant
          roots := sem.roots
          gamma := gamma
          kappa := kappa
          alpha := Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO]
          rho := rho
          queries := queries
          semantic_alpha := sem.alpha
          z := sem.z
          claim := claim
          state := t5.state }) (fun _ => rfl) p gout h

#print axioms finishWithTable
#print axioms finish_table
#print axioms source_success
end AspisR1.CuSavingsGammaTable
