import InitialArrayCallback
import ArrayFromFnCopyStable

/-! Actual source initial-array constructor segment: prepare full, add rate,
prepare the sum, then build16 lanes with the existing stable array helper. -/
set_option autoImplicit false
namespace AspisR1.InitialArrayExecution
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.AbsorptionCallback
open AspisR1.InitialArrayCallback
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskPreparedState
abbrev QM := field.QM31
abbrev callbackInst := AspisR1InitialCandidate.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

def run (full rate : QM) (openings : Openings) : Result (Array QM 16#usize) := do
  let pFull ← field.PreparedQm31Multiplier.new full
  let total ← field.QM31.add full rate
  let pTotal ← field.PreparedQm31Multiplier.new total
  array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy callbackInst
    field.QM31.ZERO (pTotal, openings, pFull)

theorem source_success (full rate : QM) (openings : Openings)
    (hf : Canonical full) (hr : Canonical rate)
    (ho : ∀ i : Fin 16, Canonical (sourceCell openings.z i)) :
    ∃ out : Array QM 16#usize, run full rate openings = .ok out ∧
      (∀ i : Fin 16, Canonical (sourceCell out i)) ∧
      ∀ i : Fin 16, decode (sourceCell out i) =
        (if i.val < 8 then decode full + decode rate else decode full) *
          decode (sourceCell openings.z i) := by
  classical
  obtain ⟨pFull, hpFull, hpreparedFull⟩ := current_prepared_new full hf
  obtain ⟨total, htotal, hctotal, hvtotal⟩ := current_qm_add_exact full rate hf hr
  obtain ⟨pTotal, hpTotal, hpreparedTotal⟩ := current_prepared_new total hctotal
  have hcallbacks : ∀ i : Fin 16, ∃ out,
      AspisR1.InitialArrayCallback.call (pTotal, openings, pFull)
        (UScalar.ofNatCore i.val (by scalar_tac)) = .ok (out, (pTotal, openings, pFull)) ∧
      Canonical out ∧ decode out =
        (if i.val < 8 then decode total else decode full) * decode (sourceCell openings.z i) := by
    intro i
    let idx : Usize := UScalar.ofNatCore i.val (by scalar_tac)
    have hidx : idx.val = i.val := by scalar_tac
    have hbound : idx.val < 16 := by rw [hidx]; exact i.isLt
    obtain ⟨out, hr, hc, hv⟩ := AspisR1.InitialArrayCallback.callback_success total full pTotal pFull
      openings idx hbound hctotal hf hpreparedTotal hpreparedFull ho
    have hfin : (⟨idx.val, hbound⟩ : Fin 16) = i := by
      apply Fin.ext
      exact hidx
    rw [hfin, hidx] at hv
    exact ⟨out, hr, hc, hv⟩
  choose values hcall hcanonical hmodel using hcallbacks
  let value : Nat → QM := fun i => if hi : i < 16 then values ⟨i, hi⟩ else field.QM31.ZERO
  have hstable : ∀ i : Usize, i.val < (16#usize).val →
      callbackInst.call_mut (pTotal, openings, pFull) i =
        .ok (value i.val, (pTotal, openings, pFull)) := by
    intro i hi
    have h : i.val < 16 := by simpa using hi
    have heq : UScalar.ofNatCore i.val (by scalar_tac) = i := by
      apply UScalar.eq_of_val_eq
      rfl
    have hc := hcall ⟨i.val, h⟩
    rw [heq] at hc
    simpa only [value, dif_pos h] using hc
  obtain ⟨out, hrun, hout⟩ := array_from_fn_copy_stable 16#usize
    field.QM31.Insts.CoreMarkerCopy callbackInst field.QM31.ZERO
    (pTotal, openings, pFull) value hstable
  have hcell : ∀ i : Fin 16, sourceCell out i = values i := by
    intro i
    have hi : i.val < (16#usize).val := by simpa using i.isLt
    have hh := hout i.val hi
    simpa only [sourceCell, value, dif_pos i.isLt] using hh
  refine ⟨out, ?_, ?_, ?_⟩
  · simp only [run, hpFull, bind_tc_ok, htotal, hpTotal, hrun]
  · intro i
    rw [hcell]
    exact hcanonical i
  · intro i
    rw [hcell, hmodel, hvtotal]

#print axioms source_success
end
end AspisR1.InitialArrayExecution
