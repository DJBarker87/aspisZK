import PathLaneSourceStep
import PathLaneArithmetic

/-! Actual literal path wrapper prefix: read bit0, construct its Boolean
residual, zero-fill17 cells and write cell0. -/
set_option autoImplicit false
namespace AspisR1.PathLaneSourcePrefix
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PathLaneSourceStep
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskConstants

abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings

def bitIndex : Fin (16#usize).val := ⟨0, by scalar_tac⟩

private theorem index_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

def runPrefix (selector : QM) (openings : Openings) : Result (QM × Array QM 17#usize) := do
  let bit ← Array.index_usize openings.z 0#usize
  let residual ← AspisR1.PathLaneArithmetic.booleanResidual selector bit
  let path ← Array.update (Array.repeat 17#usize field.QM31.ZERO) 0#usize residual
  .ok (bit, path)

theorem generated_wrapper_eq (selector : QM) (openings : Openings) :
    AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal
      selector openings = (do
        let (bit, path) ← runPrefix selector openings
        AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
          { start := 0#usize, «end» := AspisR1PathLaneCandidate.poseidon2.DIGEST_ELEMS }
          selector openings.z openings.succ_z bit path) := by
  simp only [AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal,
    runPrefix, AspisR1.PathLaneArithmetic.booleanResidual, bind_assoc_eq]
  rfl

private theorem set_canonical {N : Usize} (a : Array QM N) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : Canonical x) : CanonicalArray (a.set i x) := by
  intro j
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using j.isLt
  have hjOld : j.val < a.val.length := by simpa using j.isLt
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hjOld := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

theorem prefix_success (selector : QM) (openings : Openings)
    (hs : Canonical selector) (hz : CanonicalArray openings.z) :
    ∃ bit path, runPrefix selector openings = .ok (bit, path) ∧
      bit = cell openings.z bitIndex ∧ Canonical bit ∧ CanonicalArray path ∧
      ∀ j : Fin 17, decode (cell path j) =
        if j.val = 0 then decode selector * (decode bit * (decode bit - 1)) else 0 := by
  let bit := cell openings.z bitIndex
  have hb : Canonical bit := hz bitIndex
  have hread : Array.index_usize openings.z 0#usize = .ok bit := by
    have hzeroVal : (0#usize).val = 0 := by scalar_tac
    simpa only [bit, cell, bitIndex, hzeroVal] using
      index_ok openings.z 0#usize (by scalar_tac)
  obtain ⟨residual, hresidual, hcresidual, hvresidual⟩ :=
    AspisR1.PathLaneArithmetic.booleanResidual_success selector bit hs hb
  let zero := Array.repeat 17#usize field.QM31.ZERO
  have hzero : CanonicalArray zero := by
    intro j
    change AspisR1.ExtractedMaskTowerAdd.CanonicalQM
      ((List.replicate 17 field.QM31.ZERO)[j.val]'(by
        simpa [Array.repeat_val] using j.isLt))
    rw [List.getElem_replicate]
    exact zero_canonical
  obtain ⟨path, hwrite, hset⟩ := WP.spec_imp_exists
    (Array.update_spec zero 0#usize residual (by simp [zero, Array.repeat]))
  have hcanonical : CanonicalArray path := by
    rw [hset]
    exact set_canonical zero 0#usize residual hzero hcresidual
  refine ⟨bit, path, ?_, rfl, hb, hcanonical, ?_⟩
  · change Array.update (Array.repeat 17#usize field.QM31.ZERO) 0#usize residual = .ok path at hwrite
    simp only [runPrefix, hread, bind_tc_ok, hresidual, hwrite]
  · intro j
    rw [hset]
    by_cases hj : j.val = 0
    · have hself : cell (zero.set 0#usize residual) j = residual := by
        simp [cell, Array.set_val_eq, hj]
      rw [hself, if_pos hj]
      exact hvresidual
    · have hframe : cell (zero.set 0#usize residual) j = cell zero j := by
        simp [cell, Array.set_val_eq, List.getElem_set_ne, Ne.symm hj]
      rw [hframe, if_neg hj]
      have hzj : cell zero j = field.QM31.ZERO := by
        change (List.replicate 17 field.QM31.ZERO)[j.val]'(by
          simpa [Array.repeat_val] using j.isLt) = field.QM31.ZERO
        rw [List.getElem_replicate]
      rw [hzj, zero_decode]

#print axioms generated_wrapper_eq
#print axioms prefix_success
end
end AspisR1.PathLaneSourcePrefix
