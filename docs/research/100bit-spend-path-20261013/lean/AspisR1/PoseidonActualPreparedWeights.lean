import AspisR1.PoseidonActualLowWeights
import AspisR1.PoseidonPreparedWeightMap
import ExtractedMaskQM31Exact
import ExtractedMaskHornerStep
import ExtractedMaskTowerAdd

set_option autoImplicit false
namespace AspisR1.PoseidonActualPreparedWeights
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor
abbrev Callback := AspisR1.PoseidonPreparedWeightMap.Callback
abbrev New := field.PreparedQm31Multiplier.new

private def localAt (localWeights : Array QM 16#usize) (i : Fin 16) : QM :=
  localWeights.val[i.val]'(by simpa [localWeights.property] using i.isLt)
private def prepAt3 (a : Array Prepared 3#usize) (i : Fin 3) : Prepared :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def weightAt3 (a : Array QM 3#usize) (i : Fin 3) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)
private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩

def source (localWeights : Array QM 16#usize) : Result (Array Prepared 3#usize) := do
  let leadingLow ← Array.index_usize localWeights 0#usize
  let fullLow ← AspisR1.PoseidonActualLowWeights.fullLowSource localWeights
  let internalLow ← AspisR1.PoseidonActualLowWeights.internalLowSource localWeights
  core.array.Array.map Callback (Array.make 3#usize [leadingLow,fullLow,internalLow]) New

theorem source_success (localWeights : Array QM 16#usize)
    (hlocal : ∀ i : Fin 16, Canonical (localAt localWeights i)) :
    ∃ leadingLow fullLow internalLow : QM,
    ∃ weights : Array QM 3#usize,
    ∃ preparedWeights : Array Prepared 3#usize,
      source localWeights = .ok preparedWeights ∧
      weights = Array.make 3#usize [leadingLow,fullLow,internalLow] ∧
      Canonical leadingLow ∧ Canonical fullLow ∧ Canonical internalLow ∧
      PreparedFor (prepAt3 preparedWeights i0) leadingLow ∧
      PreparedFor (prepAt3 preparedWeights i1) fullLow ∧
      PreparedFor (prepAt3 preparedWeights i2) internalLow ∧
      Decode leadingLow = Decode (localAt localWeights 0) ∧
      Decode fullLow = AspisR1.PoseidonExplicitLowWeightFold.fullLow
        (fun i => Decode (localAt localWeights i)) ∧
      Decode internalLow = AspisR1.PoseidonExplicitLowWeightFold.internalLow
        (fun i => Decode (localAt localWeights i)) := by
  have hread0 : Array.index_usize localWeights 0#usize = .ok (localAt localWeights 0) := by
    simpa [localAt] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
      localWeights 0#usize (by decide)
  obtain ⟨fullLow,hfull,hfullCan,hfullDec⟩ :=
    AspisR1.PoseidonActualLowWeights.fullLow_source_success localWeights hlocal
  obtain ⟨internalLow,hinternal,hinternalCan,hinternalDec⟩ :=
    AspisR1.PoseidonActualLowWeights.internalLow_source_success localWeights hlocal
  let leadingLow := localAt localWeights 0
  have hleadingCan : Canonical leadingLow := hlocal 0
  obtain ⟨p0,p1,p2,hmap,hp0,hp1,hp2⟩ :=
    AspisR1.PoseidonPreparedWeightMap.prepared_map_three
      leadingLow fullLow internalLow hleadingCan hfullCan hinternalCan
  let weights : Array QM 3#usize := Array.make 3#usize [leadingLow,fullLow,internalLow]
  let preparedWeights : Array Prepared 3#usize := Array.make 3#usize [p0,p1,p2]
  refine ⟨leadingLow,fullLow,internalLow,weights,preparedWeights,?_,rfl,
    hleadingCan,hfullCan,hinternalCan,?_,?_,?_,?_,hfullDec,hinternalDec⟩
  · simp only [source,hread0,hfull,hinternal,bind_tc_ok,hmap,
      leadingLow, preparedWeights]
  · simpa [preparedWeights, prepAt3, i0, Array.make] using hp0
  · simpa [preparedWeights, prepAt3, i1, Array.make] using hp1
  · simpa [preparedWeights, prepAt3, i2, Array.make] using hp2
  · exact rfl

#print axioms source_success
end AspisR1.PoseidonActualPreparedWeights
