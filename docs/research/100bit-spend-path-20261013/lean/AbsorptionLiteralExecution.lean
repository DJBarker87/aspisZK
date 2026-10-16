import AbsorptionCallback
import ArrayFromFnCopyStable

/-! Execution and every output of the complete source absorption array,
reusing the existing stable-capture array loop theorem. -/
set_option autoImplicit false
namespace AspisR1.AbsorptionLiteralExecution
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.AbsorptionCallback
open AspisR1.ExtractedMaskQM31Exact
abbrev source := AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal
abbrev callbackInst := AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

theorem source_success (low fixed two eight nodes : QM)
    (openings : Array QM 16#usize)
    (hl : Canonical low) (hf : Canonical fixed) (ht : Canonical two)
    (he : Canonical eight) (hn : Canonical nodes)
    (ho : ∀ i : Fin 16, Canonical (sourceCell openings i)) :
    ∃ out : Array QM 16#usize,
      source low fixed two eight nodes openings = .ok out ∧
      (∀ i : Fin 16, Canonical (sourceCell out i)) ∧
      ∀ i : Fin 16, decode (sourceCell out i) =
        R0P.scheduleAbsorptionLiteral (decode low) (decode fixed) (decode two)
          (decode eight) (decode nodes) (fun j => decode (sourceCell openings j)) i := by
  classical
  have hcallbacks : ∀ i : Fin 16, ∃ out,
      call (fixed, two, eight, nodes, low, openings)
          (UScalar.ofNatCore i.val (by scalar_tac)) =
          .ok (out, (fixed, two, eight, nodes, low, openings)) ∧ Canonical out ∧
        decode out = decode low *
          blocksModel (decode fixed) (decode two) (decode eight) (decode nodes) i.val *
          decode (sourceCell openings i) := by
    intro i
    let idx : Usize := UScalar.ofNatCore i.val (by scalar_tac)
    have hidx : idx.val = i.val := by scalar_tac
    have hbound : idx.val < 16 := by rw [hidx]; exact i.isLt
    obtain ⟨out, hr, hc, hv⟩ := callback_success low fixed two eight nodes openings
      idx hbound hl hf ht he hn ho
    have hfin : (⟨idx.val, hbound⟩ : Fin 16) = i := by
      apply Fin.ext
      exact hidx
    rw [hfin, hidx] at hv
    exact ⟨out, hr, hc, hv⟩
  choose values hcall hcanonical hmodel using hcallbacks
  let value : Nat → QM := fun i => if hi : i < 16 then values ⟨i, hi⟩ else field.QM31.ZERO
  have hstable : ∀ i : Usize, i.val < (16#usize).val →
      callbackInst.call_mut (fixed, two, eight, nodes, low, openings) i =
        .ok (value i.val, (fixed, two, eight, nodes, low, openings)) := by
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
    (fixed, two, eight, nodes, low, openings) value hstable
  have hcell : ∀ i : Fin 16, sourceCell out i = values i := by
    intro i
    have hi : i.val < (16#usize).val := by simpa using i.isLt
    have hh := hout i.val hi
    simpa only [sourceCell, value, dif_pos i.isLt] using hh
  refine ⟨out, hrun, ?_, ?_⟩
  · intro i
    rw [hcell]
    exact hcanonical i
  · intro i
    rw [hcell, hmodel]
    unfold R0P.scheduleAbsorptionLiteral blocksModel
    rfl

#print axioms source_success
end
end AspisR1.AbsorptionLiteralExecution
