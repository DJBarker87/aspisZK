import PreweightedGroupArithmetic
import PreweightedLoopSlice

/-! A factored form of the exact per-group expression before the generated
add_preweighted_loop recursive call. The theorem includes actual checked packed
array reads/writes, canonicality, the modified cell and every untouched cell. -/
set_option autoImplicit false
namespace AspisR1.PreweightedGroupUpdate
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.ExtractedMaskQM31Exact

abbrev CanonicalArray {N : Usize} (a : Array QM N) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a

def runGroup {N : Usize} (packed : Array QM 24#usize)
    (group start : Usize) (values : Array QM N) : Result (Array QM 24#usize) := do
  let lanes ← array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
    (AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
    field.QM31.ZERO (group, start, values)
  let old ← Array.index_usize packed group
  let s ← lift (Array.to_slice lanes)
  let q ← field.qm31_pack_base4 s
  let next ← field.QM31.add old q
  Array.update packed group next

/-- Definitional factoring of the actual generated recursive-loop body. -/
theorem generated_loop_step {N : Usize}
    (iter : core.ops.range.RangeInclusive Usize) (packed : Array QM 24#usize)
    (start : Usize) (values : Array QM N) :
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
      iter packed start values = (do
        let (o, nextIter) ←
          core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
            core.iter.range.StepUsize iter
        match o with
        | none => .ok packed
        | some group =>
          let updated ← runGroup packed group start values
          AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
            nextIter updated start values) := by
  rw [AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted_loop.eq_def]
  simp only [runGroup, bind_assoc_eq]
  rfl

private theorem index_ok {T : Type} {N : Usize}
    (values : Array T N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize values i =
      .ok (values.val[i.val]'(by simpa [values.property] using hi)) := by
  have hidx : i.val < values.val.length := by simpa [values.property] using hi
  unfold Array.index_usize
  change (match values.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (values.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem runGroup_success {N : Usize}
    (packed : Array QM 24#usize) (group start : Usize) (values : Array QM N)
    (hgroup : group.val < 24) (hinterval : start.val + N.val ≤ 96)
    (hpacked : CanonicalArray packed) (hvalues : CanonicalArray values) :
    ∃ updated : Array QM 24#usize,
      runGroup packed group start values = .ok updated ∧
      CanonicalArray updated ∧
      decode (updated.val[group.val]'(by simpa [updated.property] using hgroup)) =
        decode (packed.val[group.val]'(by simpa [packed.property] using hgroup)) +
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
          (fun j : Fin 4 => selectedCell values start.val group.val j.val) ∧
      ∀ j : Fin 24, j.val ≠ group.val →
        updated.val[j.val]'(by simpa [updated.property] using j.isLt) =
          packed.val[j.val]'(by simpa [packed.property] using j.isLt) := by
  let old := packed.val[group.val]'(by simpa [packed.property] using hgroup)
  have hold : CurrentCanonicalQM old :=
    hpacked ⟨group.val, by simpa [packed.property] using hgroup⟩
  obtain ⟨lanes, q, next, hlanes, hq, hadd, hqCanonical, hnextCanonical, hdecode⟩ :=
    AspisR1.PreweightedGroupArithmetic.group_arithmetic_success
      values group start old hgroup hinterval hvalues hold
  have hread : Array.index_usize packed group = .ok old :=
    index_ok packed group (by simpa using hgroup)
  obtain ⟨updated, hupdate, hset⟩ := WP.spec_imp_exists
    (Array.update_spec packed group next (by simpa using hgroup))
  have hnew : updated.val[group.val]'(by simpa [updated.property] using hgroup) = next := by
    cases hset
    change (packed.val.set group.val next)[group.val]'(by simpa [packed.property] using hgroup) = next
    exact List.getElem_set_self (by simpa [packed.property] using hgroup)
  have hframe : ∀ j : Fin 24, j.val ≠ group.val →
      updated.val[j.val]'(by simpa [updated.property] using j.isLt) =
        packed.val[j.val]'(by simpa [packed.property] using j.isLt) := by
    intro j hj
    cases hset
    change (packed.val.set group.val next)[j.val]'(by simpa [packed.property] using j.isLt) =
      packed.val[j.val]'(by simpa [packed.property] using j.isLt)
    exact List.getElem_set_ne (Ne.symm hj) _
  refine ⟨updated, ?_, ?_, ?_, hframe⟩
  · unfold runGroup
    simp only [hlanes, bind_tc_ok, hread, lift, bind_tc_ok, hq, bind_tc_ok,
      hadd, bind_tc_ok, hupdate]
  · intro j
    by_cases heq : j.val = group.val
    · have hcell : updated.val[j.val] = next := by simpa [heq] using hnew
      rw [hcell]
      exact hnextCanonical
    · have hj : j.val < 24 := by simpa [updated.property] using j.isLt
      have hcell := hframe ⟨j.val, hj⟩ heq
      rw [hcell]
      exact hpacked ⟨j.val, by simpa [packed.property] using hj⟩
  · rw [hnew]
    exact hdecode

#print axioms generated_loop_step
#print axioms runGroup_success
end AspisR1.PreweightedGroupUpdate
