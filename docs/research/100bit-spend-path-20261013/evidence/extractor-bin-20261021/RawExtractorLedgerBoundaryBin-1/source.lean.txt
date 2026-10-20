import RawExtractorCostComposedBin

/-! A value refinement and the repaired size domain do not identify resource
labels with implementation work. This tests the abstract interface only;
the resource labels below are a counterexample, not an implementation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawExtractorLedgerBoundaryBin
open RawCutProverCompiler RawExtractorCostComposedV2 RawExtractorCostComposedBin

/-- Even on an empty log, output equality alone cannot discharge the ledger.
A real instrumentation/adequacy proof remains necessary after the size fix. -/
theorem value_and_size_insufficient (seed : RunView) (coins : Coins)
    (p : Parameters) (Q : Nat) :
    ∃ e : RawExtractorCostComposedBin.CostedExtractor,
      ∃ run : RunView, run.2.2 = true ∧ run.1.length ≤ Q + 1161 ∧
        ¬ RawExtractorCostComposedBin.LedgerRefinement e p Q := by
  let e : RawExtractorCostComposedBin.CostedExtractor :=
    { eval := fun run tape => (RawRecordedPublicSpendExtractorBin.extract run tape,
        { fieldOps := 0, logReads := p.readBudget + 1, bits := 0 })
      value := fun _ _ => rfl }
  let run : RunView := ([], (seed.2.1, true))
  have ha : run.2.2 = true := rfl
  have hl : run.1.length ≤ Q + 1161 := Nat.zero_le _
  refine ⟨e, run, ha, hl, ?_⟩
  intro ledger
  have hr := ledger.reads run coins ha hl
  change p.readBudget + 1 ≤ p.readBudget at hr
  omega

#print axioms value_and_size_insufficient
end AspisR1.RawExtractorLedgerBoundaryBin
end
