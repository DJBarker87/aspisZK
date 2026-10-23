from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s=(p/'ProverCommitDeployedFuel22.lean').read_text()
prefix=s[:s.index('/-- Equality of the full observable')]
prefix=prefix.replace('import R1Z.PrivacyR1HeadlineDeployed\nimport R1Z.ProverCommitFuelJoin22','import R1Z.ProverCommitDeployedFuel22').replace('namespace R1Z.ProverCommitDeployedFuel22','namespace R1Z.PrivacyR1HeadlineDeployedReal')
v=s[s.index('variable (rust :'):s.index('/-- The explicit deployed obligation.')]
v=v.replace('  [Fintype rust.IdealRand] [Nonempty rust.IdealRand]\n','')
queries=s[s.index('/-- Exact adversary-only'):s.index('def idealSeedQueries')]
ref=s[s.index('def RustProverRefinement : Prop :='):s.index('/-- Every previous certificate')]
ref=ref[:ref.index(' ∧\n')].replace('def RustProverRefinement','def RustRealRefinement')
ref=ref.replace('  (∀','  ∀',1)
assert ref.endswith(')))')
ref=ref[:-1]+'\n\n'
head=s[s.index('theorem privacy_headline_deployed\n'):s.index(' := by\n  have model')]
# Preserve the entire original numeric envelope and both numerical conclusions verbatim.
oldzk='ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)'
newzk='(∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →\n      |mean (realTest h B outputs rust adv x w) -\n        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x\n          (simE (h).transport B outputs x))| ≤'
head=head.replace('RustProverRefinement','RustRealRefinement').replace(oldzk,newzk)
# Original error expression is parenthesized: close the forall after it.
head=head.replace('ProverCommitFuelMass22.charge) ∧','ProverCommitFuelMass22.charge)) ∧',1)
body=s[s.index(' := by\n  have model'):s.index('\n#print axioms WholeRunJoin.tests')]
body=body.replace('(refinement.1 adv w hw)','(refinement adv w hw)')
a=body.index('    have hi₀ :='); b=body.index('    have hscan',a); body=body[:a]+body[b:]
a=body.index('    have idealMass'); b=body.index('    obtain ⟨hpub',a); body=body[:a]+body[b:]
a=body.index('    have t₂ :='); b=body.index('\n  · constructor',a)
body=body[:a]+'''    have spare : (0 : ℚ) ≤ 8 / (2 : ℚ)^486 +
        ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge := by
      unfold ProverCommitSeedEvent19.budget ProverCommitFuelMass22.charge
      positivity
    calc _ ≤ (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) +
          modelError W Pr L₁ L₂ := t₁.trans (add_le_add hr hmid)
         _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) +
          modelError W Pr L₁ L₂) +
          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64) +
          ProverCommitFuelMass22.charge) := le_add_of_nonneg_right spare
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
           2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge := by ring
         _ ≤ _ := add_le_add (add_le_add (add_le_add (le_refl _) hk) (le_refl _)) (le_refl _)
'''+body[b:]
end='''
/-- The original two-conjunct certificate implies the new endpoint's only
refinement premise. The second conjunct is unused. -/
theorem old_refinement_implies
    [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
    (old : ProverCommitDeployedFuel22.RustProverRefinement
      template outputs x rust observer_program) :
    RustRealRefinement template outputs x rust observer_program := old.1

#print axioms privacy_headline_deployed
#print axioms old_refinement_implies
end R1Z.PrivacyR1HeadlineDeployedReal
'''
(p/'PrivacyR1HeadlineDeployedReal.lean').write_text(prefix+v+queries+ref+'attribute [local irreducible] PrivacyR1AcctBasis.basis\n'+head+body+end)
