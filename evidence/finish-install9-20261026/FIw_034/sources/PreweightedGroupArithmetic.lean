import PreweightedLaneArray
import ExtractedMaskQmPackBase4Whole

/-! The actual per-group operations used by add_preweighted: stable four-cell
construction, checked packer and checked addition, with exact field meaning.
The outer inclusive-range traversal is a separate source proof. -/
set_option autoImplicit false
namespace AspisR1.PreweightedGroupArithmetic
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedLaneArray
open AspisR1.ExtractedMaskQM31Exact

abbrev PackMath := AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack

theorem group_arithmetic_success {N : Usize}
    (values : Array QM N) (group start : Usize) (old : QM)
    (hgroup : group.val < 24) (hinterval : start.val + N.val ≤ 96)
    (hvalues : AspisR1.SelectorExpansionCorrectness.canonicalArray values)
    (hold : CurrentCanonicalQM old) :
    ∃ lanes : Array QM 4#usize, ∃ packed next : QM,
      array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
        (AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
        field.QM31.ZERO (group, start, values) = .ok lanes ∧
      field.qm31_pack_base4 (Array.to_slice lanes) = .ok packed ∧
      field.QM31.add old packed = .ok next ∧
      CurrentCanonicalQM packed ∧ CurrentCanonicalQM next ∧
      decode next = decode old +
        PackMath (fun j : Fin 4 => selectedCell values start.val group.val j.val) := by
  obtain ⟨lanes, hlanes, hcanonical, hcells⟩ :=
    lane_array_success values group start hgroup hinterval hvalues
  have hlen : (Array.to_slice lanes).length = 4 := by
    simp [Array.to_slice, Slice.length, lanes.property]
  have hinput (j : Fin 4) :
      AspisR1.ExtractedMaskQmPackBase4Whole.inputAt (Array.to_slice lanes) hlen j =
      selectedCell values start.val group.val j.val := by
    simpa [AspisR1.ExtractedMaskQmPackBase4Whole.inputAt, Array.to_slice] using hcells j
  have hpackCanonical : ∀ j : Fin 4, CurrentCanonicalQM
      (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt (Array.to_slice lanes) hlen j) := by
    intro j
    rw [hinput]
    exact selectedCell_canonical values start.val group.val j.val hvalues
  obtain ⟨packed, hpack, hpackedCanonical, hpackDecode⟩ :=
    AspisR1.ExtractedMaskQmPackBase4Whole.qm31_pack_base4_success
      (Array.to_slice lanes) hlen hpackCanonical
  obtain ⟨next, hadd, hnextCanonical, hnextDecode⟩ :=
    current_qm_add_exact old packed hold hpackedCanonical
  refine ⟨lanes, packed, next, hlanes, hpack, hadd, hpackedCanonical, hnextCanonical, ?_⟩
  rw [hnextDecode, hpackDecode]
  have hfun : AspisR1.ExtractedMaskQmPackBase4Whole.inputAt (Array.to_slice lanes) hlen =
      (fun j : Fin 4 => selectedCell values start.val group.val j.val) := by
    funext j
    exact hinput j
  rw [hfun]

#print axioms group_arithmetic_success
end AspisR1.PreweightedGroupArithmetic
