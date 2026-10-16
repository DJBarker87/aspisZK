import ArrayFromFnCopyStable
import SelectedClaimSlice
import SelectedClaimGatherSlice
import SelectedClaimProofs

/-! Composition of the generated 84-cell gather with its exact flat callback.
The only semantic input is canonicality of the 3x28 cells that the callback
actually reads. -/
set_option autoImplicit false

namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result ControlFlow

private def selectedFlatCell
    (claims : Array (Array field.QM31 29#usize) 3#usize) (n : Nat) : field.QM31 :=
  (claims.val.getD (n / 28) (Array.repeat 29#usize field.QM31.ZERO)).val.getD
    (n % 28) field.QM31.ZERO

private theorem selectedFlatCell_eq_cell
    (claims : Array (Array field.QM31 29#usize) 3#usize)
    (n : Nat) (hn : n < 84) :
    selectedFlatCell claims n =
      (claims.val[n / 28]'(by
        have h : n / 28 < 3 := by omega
        simpa [claims.property] using h)).val[n % 28]'(by
          have hrow : n / 28 < 3 := by omega
          have hcol : n % 28 < 29 := by omega
          have hrowBound : n / 28 < claims.val.length := by
            simpa [claims.property] using hrow
          have hlen := (claims.val[n / 28]'hrowBound).property
          simpa [hlen] using hcol) := by
  have hrow : n / 28 < 3 := by omega
  have hcol : n % 28 < 29 := by omega
  have houter : n / 28 < claims.val.length := by
    simpa [claims.property] using hrow
  have hrowlen := (claims.val[n / 28]'houter).property
  have hinner : n % 28 < (claims.val[n / 28]'houter).val.length := by
    simpa [hrowlen] using hcol
  simp only [selectedFlatCell, List.getD_eq_getElem _ _ houter,
    List.getD_eq_getElem _ _ hinner]

/-- The source's `terminal_qm31` gather of 84 selected claim cells succeeds,
returns each row-major cell, and preserves the callback's captured claims.
The callback contract is discharged from the exact `call_mut` theorem. -/
theorem terminal_selected_gather_success
    (claims : Array (Array field.QM31 29#usize) 3#usize)
    (hcanonical : ∀ p : Fin 3, ∀ col : Fin 28,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        ((claims.val[p.val]'(by simpa [claims.property] using p.isLt)).val[
          col.val]'(by
            have hrowBound : p.val < claims.val.length := by
              simpa [claims.property] using p.isLt
            have hrowlen := (claims.val[p.val]'hrowBound).property
            simpa [hrowlen] using (show col.val < 29 by omega)))) :
    ∃ selected : Array field.QM31 84#usize,
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok selected ∧
      (∀ j : Fin 84,
        selected.val[j.val]'(by simpa [selected.property] using j.isLt) =
          (claims.val[j.val / 28]'(by
            have hrow : j.val / 28 < 3 := by omega
            simpa [claims.property] using hrow)).val[
              j.val % 28]'(by
                have hrow : j.val / 28 < 3 := by omega
                have hcol : j.val % 28 < 28 := by omega
                have hrowBound : j.val / 28 < claims.val.length := by
                  simpa [claims.property] using hrow
                have hlen := (claims.val[j.val / 28]'hrowBound).property
                simpa [hlen] using (show j.val % 28 < 29 by omega))) ∧
      (∀ j : Fin 84,
        AspisR1.ExtractedMaskTowerAdd.CanonicalQM
          (selected.val[j.val]'(by simpa [selected.property] using j.isLt))) := by
  let value : Nat → field.QM31 := selectedFlatCell claims
  let inst :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  have hstable : ∀ i : Std.Usize, i.val < (84#usize).val →
      inst.call_mut claims i = .ok (value i.val, claims) := by
    intro i hi
    have h84 : (84#usize).val = 84 := by scalar_tac
    rw [h84] at hi
    obtain ⟨q, hcall, hq, hcan⟩ :=
      terminal_flat_call_mut_success claims i hi hcanonical
    have hvalue : q = value i.val := by
      dsimp [value]
      rw [selectedFlatCell_eq_cell claims i.val hi, hq]
    simpa [inst, hvalue] using hcall
  obtain ⟨selected, hrun, hcells⟩ :=
    array_from_fn_copy_stable (84#usize) field.QM31.Insts.CoreMarkerCopy
      inst field.QM31.ZERO claims value hstable
  have h84 : (84#usize).val = 84 := by scalar_tac
  refine ⟨selected, hrun, ?_, ?_⟩
  · intro j
    have hj : j.val < 84 := j.isLt
    have hcell := selectedFlatCell_eq_cell claims j.val hj
    have hout := hcells j.val (by rw [h84]; exact hj)
    simpa [value, hcell] using hout
  · intro j
    have hj : j.val < 84 := j.isLt
    have hrow : j.val / 28 < 3 := by omega
    have hcol : j.val % 28 < 28 := by omega
    have hrowlen := (claims.val[j.val / 28]'(by
      simpa [claims.property] using hrow)).property
    have hcol29 : j.val % 28 < 29 := by omega
    have hcan := hcanonical ⟨j.val / 28, hrow⟩ ⟨j.val % 28, hcol⟩
    have hcell := selectedFlatCell_eq_cell claims j.val hj
    have hout := hcells j.val (by rw [h84]; exact hj)
    rw [hout]
    change AspisR1.ExtractedMaskTowerAdd.CanonicalQM (selectedFlatCell claims j.val)
    rw [hcell]
    exact hcan

#print axioms terminal_selected_gather_success

end AspisR1SelectedMaskProbe
