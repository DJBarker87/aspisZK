import InitialCallbackSlice
import AbsorptionCallback
import ExtractedMaskPreparedMul

/-! Actual initial-array callback, reusing the previously proved prepared
multiplier constructor/state and multiplication correspondence. -/
set_option autoImplicit false
namespace AspisR1.InitialArrayCallback
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.AbsorptionCallback
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskPreparedState
open AspisR1.ExtractedMaskPreparedMul
abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Prepared := field.PreparedQm31Multiplier
abbrev call := AspisR1InitialCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

theorem callback_success (fullOrRate full : QM) (pOrRate pFull : Prepared)
    (openings : Openings) (lane : Usize) (hlane : lane.val < 16)
    (hOrRate : Canonical fullOrRate) (hFull : Canonical full)
    (hpOrRate : PreparedFor pOrRate fullOrRate) (hpFull : PreparedFor pFull full)
    (ho : ∀ i : Fin 16, Canonical (sourceCell openings.z i)) :
    ∃ out, call (pOrRate, openings, pFull) lane = .ok (out, (pOrRate, openings, pFull)) ∧
      Canonical out ∧ decode out =
        (if lane.val < 8 then decode fullOrRate else decode full) *
          decode (sourceCell openings.z ⟨lane.val, hlane⟩) := by
  let current := sourceCell openings.z ⟨lane.val, hlane⟩
  have hc : Canonical current := ho ⟨lane.val, hlane⟩
  have hb : lane.val < openings.z.length := by simpa [openings.z.property] using hlane
  obtain ⟨q, hq, hvq⟩ := WP.spec_imp_exists (Array.index_usize_spec openings.z lane hb)
  have hcurrent : q = current := by
    simpa [current, sourceCell] using hvq
  rw [hcurrent] at hq
  have h8 : (8#usize).val = 8 := by scalar_tac
  by_cases hlt : lane.val < 8
  · obtain ⟨out, hmul, hco, hvo⟩ := prepared_mul_exact pOrRate fullOrRate current hOrRate hc hpOrRate
    refine ⟨out, ?_, hco, ?_⟩
    · simp only [call,
        AspisR1InitialCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
        AspisR1InitialCandidate.poseidon2.RATE, UScalar.lt_equiv, h8, hlt, if_true,
        hq, bind_tc_ok, hmul]
    · simpa only [hlt, if_true] using hvo
  · obtain ⟨out, hmul, hco, hvo⟩ := prepared_mul_exact pFull full current hFull hc hpFull
    refine ⟨out, ?_, hco, ?_⟩
    · simp only [call,
        AspisR1InitialCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
        AspisR1InitialCandidate.poseidon2.RATE, UScalar.lt_equiv, h8, hlt, if_false,
        hq, bind_tc_ok, hmul]
    · simpa only [hlt, if_false] using hvo

#print axioms callback_success
end
end AspisR1.InitialArrayCallback
