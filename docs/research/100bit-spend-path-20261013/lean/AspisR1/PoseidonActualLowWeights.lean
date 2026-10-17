import AspisR1SelectedMaskProbe.Funs
import AspisR1SelectedMaskProbe.Types
import ExtractedMaskQM31Exact
import ExtractedMaskTowerAdd
import ExtractedMaskHornerStep
import AspisR1.PoseidonExplicitLowWeightFold

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe

set_option autoImplicit false

namespace AspisR1.PoseidonActualLowWeights

/- This source slice is the exact generated `full_low` and `internal_low`
   binding sequence in candidate Funs SHA f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c,
   translated from candidate state_only_poseidon.rs SHA
   82d54bbade8d81899c64ede23befce8b240b881d61b144e769c0d0e16ab5cff9.
   It intentionally preserves the initial ZERO add and source operation order. -/

abbrev QM := field.QM31
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

def localAt (localWeights : Array QM 16#usize) (i : Fin 16) : QM :=
  localWeights.val[i.val]'(by simpa [localWeights.property] using i.isLt)

def fullLowSource (localWeights : Array QM 16#usize) : Result QM := do
  let q ← Array.index_usize localWeights 1#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize localWeights 9#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize localWeights 10#usize
  field.QM31.add q3 q4

def internalLowSource (localWeights : Array QM 16#usize) : Result QM := do
  let q ← Array.index_usize localWeights 2#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize localWeights 3#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize localWeights 4#usize
  let q5 ← field.QM31.add q3 q4
  let q6 ← Array.index_usize localWeights 5#usize
  let q7 ← field.QM31.add q5 q6
  let q8 ← Array.index_usize localWeights 6#usize
  let q9 ← field.QM31.add q7 q8
  let q10 ← Array.index_usize localWeights 7#usize
  let q11 ← field.QM31.add q9 q10
  let q12 ← Array.index_usize localWeights 8#usize
  field.QM31.add q11 q12

private theorem zero_canonical : CanonicalQM field.QM31.ZERO := by
  change AspisR1.ExtractedMaskTowerAdd.CanonicalQM field.QM31.ZERO
  norm_num [AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
    AspisR1.ExtractedMaskTowerAdd.P, field.QM31.ZERO]

private theorem decode_zero : AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ZERO = 0 := by
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode, field.QM31.ZERO]

theorem fullLow_source_success (localWeights : Array QM 16#usize)
    (hlocal : ∀ i : Fin 16, CanonicalQM (localAt localWeights i)) :
    ∃ out : QM, fullLowSource localWeights = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        AspisR1.PoseidonExplicitLowWeightFold.fullLow
          (fun i => AspisR1.ExtractedMaskQM31Exact.decode (localAt localWeights i)) := by
  let x1 := localAt localWeights 1
  let x9 := localAt localWeights 9
  let x10 := localAt localWeights 10
  have hr1 : Array.index_usize localWeights 1#usize = .ok x1 := by
    simpa [x1, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 1#usize (by decide)
  have hr9 : Array.index_usize localWeights 9#usize = .ok x9 := by
    simpa [x9, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 9#usize (by decide)
  have hr10 : Array.index_usize localWeights 10#usize = .ok x10 := by
    simpa [x10, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 10#usize (by decide)
  have hz : CanonicalQM field.QM31.ZERO := zero_canonical
  obtain ⟨a, ha, hacan, hadec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      field.QM31.ZERO x1 hz (hlocal 1)
  obtain ⟨b, hb, hbcan, hbdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact a x9 hacan (hlocal 9)
  obtain ⟨out, hout, houtcan, houtdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact b x10 hbcan (hlocal 10)
  refine ⟨out, ?_, houtcan, ?_⟩
  · simp only [fullLowSource, hr1, ha, hr9, hb, hr10, hout, bind_tc_ok]
  · change AspisR1.ExtractedMaskQM31Exact.decode out = _
    rw [houtdec, hbdec, hadec, decode_zero]
    simpa [x1, x9, x10, localAt, AspisR1.PoseidonExplicitLowWeightFold.fullLow_explicit]

theorem internalLow_source_success (localWeights : Array QM 16#usize)
    (hlocal : ∀ i : Fin 16, CanonicalQM (localAt localWeights i)) :
    ∃ out : QM, internalLowSource localWeights = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        AspisR1.PoseidonExplicitLowWeightFold.internalLow
          (fun i => AspisR1.ExtractedMaskQM31Exact.decode (localAt localWeights i)) := by
  let x2 := localAt localWeights 2
  let x3 := localAt localWeights 3
  let x4 := localAt localWeights 4
  let x5 := localAt localWeights 5
  let x6 := localAt localWeights 6
  let x7 := localAt localWeights 7
  let x8 := localAt localWeights 8
  have hr2 : Array.index_usize localWeights 2#usize = .ok x2 := by
    simpa [x2, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 2#usize (by decide)
  have hr3 : Array.index_usize localWeights 3#usize = .ok x3 := by
    simpa [x3, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 3#usize (by decide)
  have hr4 : Array.index_usize localWeights 4#usize = .ok x4 := by
    simpa [x4, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 4#usize (by decide)
  have hr5 : Array.index_usize localWeights 5#usize = .ok x5 := by
    simpa [x5, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 5#usize (by decide)
  have hr6 : Array.index_usize localWeights 6#usize = .ok x6 := by
    simpa [x6, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 6#usize (by decide)
  have hr7 : Array.index_usize localWeights 7#usize = .ok x7 := by
    simpa [x7, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 7#usize (by decide)
  have hr8 : Array.index_usize localWeights 8#usize = .ok x8 := by
    simpa [x8, localAt] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok localWeights 8#usize (by decide)
  have hz : CanonicalQM field.QM31.ZERO := zero_canonical
  obtain ⟨a, ha, hacan, hadec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact field.QM31.ZERO x2 hz (hlocal 2)
  obtain ⟨b, hb, hbcan, hbdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact a x3 hacan (hlocal 3)
  obtain ⟨c, hc, hccan, hcdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact b x4 hbcan (hlocal 4)
  obtain ⟨d, hd, hdcan, hddec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact c x5 hccan (hlocal 5)
  obtain ⟨e, he, hecan, hedec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact d x6 hdcan (hlocal 6)
  obtain ⟨f, hf, hfcan, hfdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact e x7 hecan (hlocal 7)
  obtain ⟨out, hout, houtcan, houtdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact f x8 hfcan (hlocal 8)
  refine ⟨out, ?_, houtcan, ?_⟩
  · simp only [internalLowSource, hr2, ha, hr3, hb, hr4, hc, hr5, hd,
      hr6, he, hr7, hf, hr8, hout, bind_tc_ok]
  · change AspisR1.ExtractedMaskQM31Exact.decode out = _
    rw [houtdec, hfdec, hedec, hddec, hcdec, hbdec, hadec, decode_zero]
    simpa [x2, x3, x4, x5, x6, x7, x8, localAt,
      AspisR1.PoseidonExplicitLowWeightFold.internalLow,
      List.foldl_cons, AspisR1.ExtractedMaskQM31Exact.decode]

#print axioms fullLow_source_success
#print axioms internalLow_source_success

end AspisR1.PoseidonActualLowWeights
