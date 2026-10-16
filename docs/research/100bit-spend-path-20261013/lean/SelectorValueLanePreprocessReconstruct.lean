import SelectorValueLanePreprocessCanonical
import SelectorReconstructIndexedSource

/-! Compose the actual three preprocessing loops with the actual indexed
`reconstruct_10` wrappers. This is the caller-facing construction needed
before the final selector range writes. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLanePreprocessReconstruct

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) := AspisR1.SelectorExpansionCorrectness.canonicalArray a

/-- Successful preprocessing leaves the openings unchanged, preserves the
range's canonicality, and each generated reconstruction call returns the
retained ten-cell polynomial on its corresponding opening array. -/
theorem preprocessing_reconstructs_three_openings
    (openings : Openings) (range : Array QM 33#usize)
    (openings1 openings2 openings3 : Openings)
    (range1 range2 range3 : Array QM 33#usize)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z)
    (hrange : CanonicalArray range)
    (h0 : AspisR1.SelectorValueLanePreprocessCanonical.Loop0
      openings range 0#usize = .ok (openings1, range1))
    (h1 : AspisR1.SelectorValueLanePreprocessCanonical.Loop1
      openings1 range1 0#usize = .ok (openings2, range2))
    (h2 : AspisR1.SelectorValueLanePreprocessCanonical.Loop2
      openings2 range2 0#usize = .ok (openings3, range3)) :
    openings3 = openings ∧ CanonicalArray range3 ∧
    ∃ rz rs rx,
      AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
        openings3.z = .ok rz ∧ Canonical rz ∧
      AspisR1.ExtractedMaskQM31Exact.decode rz =
        R0P.valueReconstruct10
          (fun i : Fin 16 => AspisR1.ExtractedMaskQM31Exact.decode
            (openings3.z.val[i.val]'(by simpa [openings3.z.property] using i.isLt))) ∧
      AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
        openings3.succ_z = .ok rs ∧ Canonical rs ∧
      AspisR1.ExtractedMaskQM31Exact.decode rs =
        R0P.valueReconstruct10
          (fun i : Fin 16 => AspisR1.ExtractedMaskQM31Exact.decode
            (openings3.succ_z.val[i.val]'(by simpa [openings3.succ_z.property] using i.isLt))) ∧
      AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
        openings3.xor12_z = .ok rx ∧ Canonical rx ∧
      AspisR1.ExtractedMaskQM31Exact.decode rx =
        R0P.valueReconstruct10
          (fun i : Fin 16 => AspisR1.ExtractedMaskQM31Exact.decode
            (openings3.xor12_z.val[i.val]'(by simpa [openings3.xor12_z.property] using i.isLt))) := by
  obtain ⟨hsame, hrange3⟩ :=
    AspisR1.SelectorValueLanePreprocessCanonical.three_preprocessing_loops_preserve_canonicality
      openings range openings1 openings2 openings3 range1 range2 range3
      hopenZ hopenSucc hopenXor hrange h0 h1 h2
  subst openings3
  obtain ⟨rz, hrz, hcz, hvz⟩ :=
    AspisR1.SelectorReconstructIndexedSource.reconstruct_10_success openings.z hopenZ
  obtain ⟨rs, hrs, hcs, hvs⟩ :=
    AspisR1.SelectorReconstructIndexedSource.reconstruct_10_success openings.succ_z hopenSucc
  obtain ⟨rx, hrx, hcx, hvx⟩ :=
    AspisR1.SelectorReconstructIndexedSource.reconstruct_10_success openings.xor12_z hopenXor
  exact ⟨rfl, hrange3, rz, rs, rx, hrz, hcz, hvz, hrs, hcs, hvs, hrx, hcx, hvx⟩

#print axioms preprocessing_reconstructs_three_openings
end AspisR1.SelectorValueLanePreprocessReconstruct
