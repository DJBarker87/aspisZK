import SelectorValueLanePreprocessCanonical
import ExtractedMaskConstants

/-! Specialization of preprocessing canonicality to the generated zero-filled
range initializer. Successful loop equations and canonical opening arrays stay
explicit; only the initial range canonicality is discharged here. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLanePreprocessZeroInit

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev CanonicalArray {n : Usize} (a : Array QM n) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Loop0 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
abbrev Loop1 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
abbrev Loop2 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2

theorem zero_range_canonical :
    CanonicalArray (Array.repeat 33#usize field.QM31.ZERO) := by
  intro i
  change AspisR1.ExtractedMaskTowerAdd.CanonicalQM
    ((List.replicate 33 field.QM31.ZERO)[i.val]'(by
      simpa [Array.repeat_val] using i.isLt))
  have hcell : (List.replicate 33 field.QM31.ZERO)[i.val]'(by
      simpa [Array.repeat_val] using i.isLt) = field.QM31.ZERO := by
    rw [List.getElem_replicate]
  rw [hcell]
  exact AspisR1.ExtractedMaskConstants.zero_canonical

theorem three_preprocessing_loops_preserve_zero_init
    (openings : Openings)
    (openings1 openings2 openings3 : Openings)
    (range1 range2 range3 : Array QM 33#usize)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z)
    (h0 : Loop0 openings (Array.repeat 33#usize field.QM31.ZERO) 0#usize =
      .ok (openings1, range1))
    (h1 : Loop1 openings1 range1 0#usize = .ok (openings2, range2))
    (h2 : Loop2 openings2 range2 0#usize = .ok (openings3, range3)) :
    openings3 = openings ∧ CanonicalArray range3 := by
  exact AspisR1.SelectorValueLanePreprocessCanonical.three_preprocessing_loops_preserve_canonicality
    openings (Array.repeat 33#usize field.QM31.ZERO)
    openings1 openings2 openings3 range1 range2 range3
    hopenZ hopenSucc hopenXor zero_range_canonical h0 h1 h2

#print axioms zero_range_canonical
#print axioms three_preprocessing_loops_preserve_zero_init
end AspisR1.SelectorValueLanePreprocessZeroInit
