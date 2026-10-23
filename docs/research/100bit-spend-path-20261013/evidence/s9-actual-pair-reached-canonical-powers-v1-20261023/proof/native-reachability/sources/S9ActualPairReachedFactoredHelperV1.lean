import S9PairLoop1SelfComponentV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairReachedFactoredHelperV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev A4 := Array W 4#usize
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

/-- The helper success is extracted from the same accepted actual Pair call,
including its actual powers producers. S2/two-fold admission is explicit. -/
theorem actual_pair_success_reaches_factored_helper
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hs2 : self.variant = transport.Variant.S2) (hfold : Slice.len alpha = 2#usize)
    (h : weights.Weights.pair self alpha f kappa = .ok (.Ok out)) :
    ∃ (a0 a1 : W) (ap0 ap1 : A4) (libra : Array W 4#usize),
      Slice.index_usize alpha 0#usize = .ok a0 ∧
      weights.powers 4#usize a0 = .ok ap0 ∧
      Slice.index_usize alpha 1#usize = .ok a1 ∧
      weights.powers 4#usize a1 = .ok ap1 ∧
      weights.factored_s2_libra_weights ap0 ap1 self.extra = .ok libra := by
  unfold weights.Weights.pair at h
  obtain ⟨n,hn,h⟩ := bind_success _ _ _ h
  obtain ⟨expected,hexpected,h⟩ := bind_success _ _ _ h
  split at h
  · cases h
  · obtain ⟨a0,ha0,h⟩ := bind_success _ _ _ h
    obtain ⟨ap0,hap0,h⟩ := bind_success _ _ _ h
    have h21 : (2#usize : Usize) ≠ 1#usize := by
      intro heq
      have hv := congrArg UScalar.val heq
      simp at hv
    simp only [hfold,if_neg h21] at h
    obtain ⟨ap1,hap1producer,h⟩ := bind_success _ _ _ h
    obtain ⟨a1,ha1,hap1⟩ := bind_success _ _ _ hap1producer
    obtain ⟨reserve,hreserve,h⟩ := bind_success _ _ _ h
    cases reserve with
    | Err e => cases h
    | Ok scratch =>
      obtain ⟨shared,hshared,h⟩ := bind_success _ _ _ h
      obtain ⟨processed,hprocessed,h⟩ := bind_success _ _ _ h
      rcases processed with ⟨r1,scratch1,parts1⟩
      cases r1 with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
      | Ok unit =>
        obtain ⟨cf,hcf,h⟩ := bind_success
          (core.result.Result.Insts.CoreOpsTry.branch (E := verifier.Error) (.Ok unit)) _ _ h
        have hcf' : cf = .Continue unit := (Result.ok.inj hcf).symm
        cases hcf'
        cases shared with
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte] at h
          obtain ⟨low,hlow,h⟩ := bind_success _ _ _ h
          obtain ⟨inactive,hinactive,h⟩ := bind_success _ _ _ h
          obtain ⟨parts,hparts,h⟩ := bind_success _ _ _ h
          have heq : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant
              transport.Variant.S2 = .ok true := by rw [hs2]; simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq]
          simp only [heq,bind_tc_ok,↓reduceIte] at h
          obtain ⟨libra,hlibra,h⟩ := bind_success _ _ _ h
          exact ⟨a0,a1,ap0,ap1,libra,ha0,hap0,ha1,hap1,hlibra⟩
        | true =>
          simp only [↓reduceIte] at h
          obtain ⟨pair,hpair,h⟩ := bind_success _ _ _ h
          rcases pair with ⟨self1,common1⟩
          have hself := AspisR1S9PairLoop1SelfComponentV3.pair_loop1_first_component
            _ self self1 _ common1 hpair
          subst self1
          obtain ⟨partials,hpartials,h⟩ := bind_success _ _ _ h
          cases partials with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at h
            cases h
          | Ok partials =>
            obtain ⟨cf,hcf,h⟩ := bind_success
              (core.result.Result.Insts.CoreOpsTry.branch (E := verifier.Error) (.Ok partials)) _ _ h
            have hcf' : cf = .Continue partials := (Result.ok.inj hcf).symm
            cases hcf'
            obtain ⟨high,hhigh,h⟩ := bind_success _ _ _ h
            rcases high with ⟨rhigh,parts2⟩
            cases rhigh with
            | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at h
              cases h
            | Ok unit =>
              obtain ⟨cf,hcf,h⟩ := bind_success
                (core.result.Result.Insts.CoreOpsTry.branch (E := verifier.Error) (.Ok unit)) _ _ h
              have hcf' : cf = .Continue unit := (Result.ok.inj hcf).symm
              cases hcf'
              obtain ⟨low,hlow,h⟩ := bind_success _ _ _ h
              obtain ⟨inactive,hinactive,h⟩ := bind_success _ _ _ h
              obtain ⟨parts,hparts,h⟩ := bind_success _ _ _ h
              have heq : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant
                  transport.Variant.S2 = .ok true := by rw [hs2]; simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq]
              simp only [heq,bind_tc_ok,↓reduceIte] at h
              obtain ⟨libra,hlibra,h⟩ := bind_success _ _ _ h
              exact ⟨a0,a1,ap0,ap1,libra,ha0,hap0,ha1,hap1,hlibra⟩

#print axioms actual_pair_success_reaches_factored_helper
end AspisR1S9ActualPairReachedFactoredHelperV1
