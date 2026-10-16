import InitialVariantSlice
import OccupancyExpectedBridge
import ExtractedMaskQM31Exact
import ExtractedMaskConstants
import R0P.Schedule

/-! The checked actual variant helper, with all four returned values canonical
and matching the retained schedule tuple in source operation order. -/
set_option autoImplicit false
namespace AspisR1.InitialVariantExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskConstants
abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := CurrentCanonicalQM
abbrev Variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant
abbrev source := AspisR1InitialVariantCandidate.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
abbrev modelVariant := AspisR1.OccupancyExpectedBridge.modelVariant

def decodeTuple (t : QM × QM × QM × QM) : ExactQM × ExactQM × ExactQM × ExactQM :=
  (decode t.1, decode t.2.1, decode t.2.2.1, decode t.2.2.2)

theorem source_success (v : Variant) (h27 h28 h29 : QM)
    (hc27 : Canonical h27) (hc28 : Canonical h28) (hc29 : Canonical h29) :
    ∃ out : QM × QM × QM × QM,
      source v h27 h28 h29 = .ok out ∧
      Canonical out.1 ∧ Canonical out.2.1 ∧ Canonical out.2.2.1 ∧ Canonical out.2.2.2 ∧
      decodeTuple out = R0P.scheduleVariantSelectors (modelVariant v)
        (decode h27) (decode h28) (decode h29) := by
  obtain ⟨sum, hsum, hcsum, hvsum⟩ := current_qm_add_exact h27 h28 hc27 hc28
  cases v with
  | PrivateTransfer =>
    refine ⟨(h27, field.QM31.ZERO, sum, h29), ?_, hc27, zero_canonical, hcsum, hc29, ?_⟩
    · simp only [source,
        AspisR1InitialVariantCandidate.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors,
        hsum, bind_tc_ok]
    · simp only [decodeTuple, modelVariant, AspisR1.OccupancyExpectedBridge.modelVariant,
        R0P.scheduleVariantSelectors, zero_decode, hvsum]
  | Withdrawal =>
    obtain ⟨sum1, hsum1, hcsum1, hvsum1⟩ := current_qm_add_exact sum h29 hcsum hc29
    refine ⟨(field.QM31.ZERO, sum1, field.QM31.ZERO, field.QM31.ZERO), ?_,
      zero_canonical, hcsum1, zero_canonical, zero_canonical, ?_⟩
    · simp only [source,
        AspisR1InitialVariantCandidate.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors,
        hsum, bind_tc_ok, hsum1]
    · simp only [decodeTuple, modelVariant, AspisR1.OccupancyExpectedBridge.modelVariant,
        R0P.scheduleVariantSelectors, zero_decode, hvsum1, hvsum]

#print axioms source_success
end
end AspisR1.InitialVariantExact
