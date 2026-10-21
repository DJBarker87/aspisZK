# Historical initial endpoint construction (J8686). Later corrections are
# retained in the attempt snapshots and final endpoint-after.lean.txt.
from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean')
e=Path(__file__).resolve().parent.parent
s=(e/'endpoint-before.lean.txt').read_text()
s=s.replace('import R1Z.ProverCommitFixedEndpoint','import R1Z.ProverCommitSeedJoin19\nimport R1Z.ProverCommitObserverQueries19\nimport R1Z.ProverCommitFixedEndpoint',1)
start=s.index('/-- The explicit deployed obligation.')
end=s.index('\nattribute [local irreducible] PrivacyR1AcctBasis.basis',start)
old=s[start:end]
legacy=old.replace('def RustProverRefinement','def LegacyRustProverRefinement')
helpers='''
/-- Exact adversary-only query suffix of the underlying ordered source. -/
def realSeedQueries (adv : rust.Adversary) (w : h.Instance) : source.RealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.real W Pr 8
    (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x w

def idealSeedQueries (adv : rust.Adversary) : source.IdealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.ideal W 8 eight_pos
    (P_R1 (h).transport B hB) (simE (h).transport B outputs x)
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x

'''
new=old.replace('existing realBad/selectedBad, not predicates chosen by the implementation.',
'''fixed parser events augmented with a single global seed-guess event on an
independently retained model seed. Query functions are fixed by the model.''').replace('(WholeRunJoin','(ProverCommitSeedJoin19.RunJoin')
new=new.replace('(QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)))',
'(QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)\n      (realSeedQueries template outputs x rust observer_program adv w)))')
new=new.replace('QueryScanIdealHistory.selectedBad))',
'QueryScanIdealHistory.selectedBad\n      (idealSeedQueries template outputs x rust observer_program adv)))')
weak='''
/-- Every previous certificate still suffices. The independent seed is added
by product extension, so this is an actual implication between premises. -/
theorem legacy_refinement_implies
    (old : LegacyRustProverRefinement template outputs x rust observer_program) :
    RustProverRefinement template outputs x rust observer_program := by
  constructor
  · intro adv w hw
    let join := Classical.choice (old.1 adv w hw)
    exact ⟨ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement⟩
  · intro adv
    let join := Classical.choice (old.2 adv)
    exact ⟨ProverCommitSeedJoin19.of_old _ _ _ _ join.cp join.agreement⟩

'''
s=s[:start]+legacy+helpers+new+weak+s[end:]
# Add the two explicit charges to each displayed amount in the endpoint.
a=s.index('theorem privacy_headline_deployed')
b=s.index(' := by',a)
sig=s[a:b]
# Each freshness term ends in + 1); there are five occurrences.
sig=sig.replace('+ 1)', '+ 1) + 2 * ProverCommitSeedEvent19.budget (2^64)')
s=s[:a]+sig+s[b:]
a=s.index('    have hr := QueryScanRealLazyJoin.join_le')
b=s.index('    obtain ⟨hpub, hs⟩',a)
s=s[:a]+'''    have hr₀ := ProverCommitSeedJoin19.test_bound
      (Classical.choice (refinement.1 adv w hw)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.real_bound W Pr 8
        (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs _ x w r)
    have hi₀ := ProverCommitSeedJoin19.test_bound
      (Classical.choice (refinement.2 adv)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.ideal_bound W 8 eight_pos
        (P_R1 (h).transport B hB) (simE (h).transport B outputs x) _ x r)
    have hscan : 8 * scanProbability ≤ 8 / (2 : ℚ)^486 := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
    have hr := hr₀.trans (add_le_add_right
      ((ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w).trans
        (add_le_add_left hscan _)) (ProverCommitSeedEvent19.budget (2^64)))
    have idealMass : eventMass (fun r => ∃ i : Fin 8, QueryScanIdealHistory.selectedBad i r) ≤
        8 * scanProbability := by
      exact R0Z.FsAbortBounds.mass_exists_le_card _ _
        (fun i => QueryScanIdealHistory.selected_bad_mass i)
    have hi := hi₀.trans (add_le_add_right (idealMass.trans hscan)
      (ProverCommitSeedEvent19.budget (2^64)))
''' +s[b:]
a=s.index('    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget')
s=s[:a]+'''    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64)) + modelError W Pr L₁ L₂) +
          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64)) :=
            t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
           2 * ProverCommitSeedEvent19.budget (2^64) := by ring
         _ ≤ _ := add_le_add_right (add_le_add (le_refl _) hk) _
  · constructor
    · exact add_le_add_right model.2.1 _
    · apply (add_le_add_right model.2.1 _).trans_lt
      exact ProverCommitSeedJoin19.total_lt_target
        (Nat.le_trans (Nat.add_le_add_right hM 1) (by norm_num)) (Nat.le_refl _)

#print axioms WholeRunJoin.tests
#print axioms legacy_refinement_implies
#print axioms privacy_headline_deployed
end R1Z.PrivacyR1HeadlineDeployed
'''
p.write_text(s)
