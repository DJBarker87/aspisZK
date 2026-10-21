from pathlib import Path
import re
P = Path(__file__).resolve().parents[2]
base = (P/'lean/R1FinalSoundness.lean').read_text()
old = (P/'lean/R1FinalSoundnessHeadline.lean').read_text()
fields = re.findall(r'^  (\w+) : Prop$',base.split('structure BoundaryStatements where')[1].split('structure BoundaryEvidence')[0], re.M)
assert fields[-1] == 'M10_uniform'
fields = fields[:-1]
header = old.split('theorem final_soundness')[0]
header = header.replace('import R1FinalSoundnessBinPerQueryTag\nimport R9PoolConcreteExperiment', 'import R1FinalSoundnessBinPerQueryM10Closed')
header = re.sub(r'/\-![\s\S]*?\-/', '/-! Headline v2: compose the existing logical Pool headline and closed M10\nledger, retaining every non-M10 evidence field and source law. -/', header)
header = header.replace('namespace AspisR1.R1FinalSoundnessHeadline', 'namespace AspisR1.R1FinalSoundnessHeadlineV2\nattribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count\n  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget')
header = header.replace('abbrev BoundaryStatements := R1FinalSoundness.BoundaryStatements\nabbrev BoundaryEvidence := R1FinalSoundness.BoundaryEvidence', '''/-- The v1 boundary inventory with only M10_uniform deleted. -/
structure BoundaryStatements where
'''+''.join(f'  {f} : Prop\n' for f in fields)+'''
/-- The v1 evidence inventory with only h_M10_uniform deleted. -/
structure BoundaryEvidence (s : BoundaryStatements) : Prop where
'''+''.join(f'  h_{f} : s.{f}\n' for f in fields)+'''
/-- Internal compatibility adapter; no claim about the caller's M10 proposition. -/
def legacyStatements (s : BoundaryStatements) : R1FinalSoundness.BoundaryStatements where
'''+''.join(f'  {f} := s.{f}\n' for f in fields)+'''  M10_uniform := True

def legacyEvidence {s : BoundaryStatements} (h : BoundaryEvidence s) :
    R1FinalSoundness.BoundaryEvidence (legacyStatements s) where
'''+''.join(f'  h_{f} := h.h_{f}\n' for f in fields)+'''  h_M10_uniform := True.intro

/-- Deleting the field weakens the evidence requirement, without replacements. -/
def ofLegacy (s : R1FinalSoundness.BoundaryStatements)
    (h : R1FinalSoundness.BoundaryEvidence s) :
    BoundaryEvidence {'''+', '.join(f'{f} := s.{f}' for f in fields)+'''} where
'''+''.join(f'  h_{f} := h.h_{f}\n' for f in fields))
statement = old.split('theorem final_soundness')[1].split(' := by')[0]
statement = statement.replace('    (e : RawExtractorCostComposedBin.CostedExtractor) (p : Parameters)\n    /- Size-restricted M10 adequacy; length is independent of distinct reads. -/\n    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement e p Q)\n', '')
statement = statement.replace('e.eval', 'ActualCostedExtractorM10.extractor.eval').replace('(p.attemptBudget : ℚ)', '((CostedAllocationLedgerM10.params Q).attemptBudget : ℚ)')
proof = ''' := by
  exact R1FinalSoundnessBinPerQueryM10Closed.final_soundness
    D d P Q tape policy hqueries (legacyStatements s) (legacyEvidence evidence) source
    (fun _ => h_R16_instance evidence) h_R13 h_R14_backend h_R15_writer h_R3_semantic
    (fun _ => h_Rwire_tag evidence) (fun _ => h_M10_log_length evidence)

/-- The same accepted recorded experiment has the explicit cubic cost bound.
This composes the closed direct bound and finite-tape mean; no new cost premise. -/
theorem accepted_cost_cubic
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161) :
    ∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤
          ((4 * CostedAllocationLedgerM10.scale^3 * (Q+1162)^3 : Nat) : ℚ) := by
  intro H ha
  have pointwise (coins : Coins) :
      ((ActualCostedExtractorM10.extractor.eval (eval H (recorded D d P)) coins).2.total : ℚ) ≤
        ((4 * CostedAllocationLedgerM10.scale^3 * (Q+1162)^3 : Nat) : ℚ) := by
    have hb := ClosedAllocationLedgerM10.direct_bound Q (eval H (recorded D d P)) coins ha
      (h_M10_log_length evidence H ha)
    unfold ActualCostedExtractorM10.extractor
    change ((ActualResourceEvalM10.eval (eval H (recorded D d P)) coins).2.total : ℚ) ≤ _
    exact_mod_cast hb
  exact (FS.mean_mono pointwise).trans (le_of_eq (AspisV8R19.OracleResampling.mean_const _))

#print axioms legacyStatements
#print axioms legacyEvidence
#print axioms ofLegacy
#print axioms final_soundness
#print axioms accepted_cost_cubic
end AspisR1.R1FinalSoundnessHeadlineV2
end
'''
(P/'lean/R1FinalSoundnessHeadlineV2.lean').write_text(header+'theorem final_soundness'+statement+proof)
