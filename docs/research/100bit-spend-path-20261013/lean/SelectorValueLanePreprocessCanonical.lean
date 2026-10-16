import SelectorValueLaneLoops012Slice
import SelectorValueLaneLoop0CanonicalOpenings
import SelectorValueLaneLoop1CanonicalOpenings
import SelectorValueLaneLoop2CanonicalOpenings
import ExtractedMaskConstants

/-! Composition of the three generated preprocessing loops. The hypotheses
are their actual successful-result equations; canonicality of the three
opening arrays and the zero-filled range is propagated through the bodies. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLanePreprocessCanonical

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev CanonicalArray {n : Usize} (a : Array QM n) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Loop0 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
abbrev Loop1 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
abbrev Loop2 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2

theorem three_preprocessing_loops_preserve_canonicality
    (openings : Openings) (range : Array QM 33#usize)
    (openings1 openings2 openings3 : Openings)
    (range1 range2 range3 : Array QM 33#usize)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z)
    (hrange : CanonicalArray range)
    (h0 : Loop0 openings range 0#usize = .ok (openings1, range1))
    (h1 : Loop1 openings1 range1 0#usize = .ok (openings2, range2))
    (h2 : Loop2 openings2 range2 0#usize = .ok (openings3, range3)) :
    openings3 = openings ∧ CanonicalArray range3 := by
  have hspan0 : 0 + 10 = 10 := by omega
  obtain ⟨ho1, hrange1⟩ :=
    AspisR1.SelectorValueLaneLoop0CanonicalOpenings.loop0_success_preserves_canonical_fuel_openings
      10 openings range 0#usize openings1 range1 hspan0 hopenZ hrange h0
  have h1' : Loop1 openings range1 0#usize = .ok (openings2, range2) := by
    simpa [ho1] using h1
  have hspan1 : 0 + 10 = 10 := by omega
  obtain ⟨ho2, hrange2⟩ :=
    AspisR1.SelectorValueLaneLoop1CanonicalOpenings.loop1_success_preserves_canonical_fuel_openings
      10 openings range1 0#usize openings2 range2 hspan1 hopenSucc hrange1 h1'
  have h2' : Loop2 openings range2 0#usize = .ok (openings3, range3) := by
    simpa [ho2] using h2
  have hspan2 : 0 + 10 = 10 := by omega
  obtain ⟨ho3, hrange3⟩ :=
    AspisR1.SelectorValueLaneLoop2CanonicalOpenings.loop2_success_preserves_canonical_fuel_openings
      10 openings range2 0#usize openings3 range3 hspan2 hopenXor hrange2 h2'
  exact ⟨ho3, hrange3⟩

#print axioms three_preprocessing_loops_preserve_canonicality
end AspisR1.SelectorValueLanePreprocessCanonical
