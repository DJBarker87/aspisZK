import SelectorReconstructIndexedSource
import SelectorValueLaneTailConstants
import SelectorValueLaneTailWritesCanonical
import EqualityValueAdapter
import ExtractedMaskScalarExact
import ExtractedMaskConstants

/-! Execute the reconstruction and three tail writes used to finish the
33-cell value range. The theorem derives checked calls from canonical source
arrays rather than assuming those calls succeeded. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneTailExecution

noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {N : Usize} (a : Array QM N) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def decodedOpening (a : Array QM 16#usize) : Fin 16 → ExactQM :=
  fun i => decode (a.val[i.val]'(by simpa [a.property] using i.isLt))

def reconstructModel (a : Array QM 16#usize) : ExactQM :=
  R0P.valueReconstruct10 (decodedOpening a)

def scale10 : M31 := AspisR1.SelectorValueLaneTailConstants.scale10
def scale20 : M31 := AspisR1.SelectorValueLaneTailConstants.scale20

/-- The actual source tail after preprocessing: three reverse reconstructions,
checked shifts, field operations, and the three array writes. -/
def tailConstruction (openings : Openings) (range3 : Array QM 33#usize) :
    Result (Array QM 33#usize) := do
  let q5 ← AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings.z
  let q6 ← AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings.succ_z
  let i ← (1#u32 <<< 10#i32 : Result U32)
  let q7 ← field.QM31.mul_m31 q6 i
  let q8 ← field.QM31.add q5 q7
  let q9 ← AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings.xor12_z
  let i1 ← (1#u32 <<< 20#i32 : Result U32)
  let q10 ← field.QM31.mul_m31 q9 i1
  let reconstructed ← field.QM31.add q8 q10
  let q11 ← Array.index_usize openings.z 10#usize
  let q12 ← field.QM31.sub q11 reconstructed
  let range4 ← Array.update range3 30#usize q12
  let q13 ← Array.index_usize openings.succ_z 10#usize
  let range5 ← Array.update range4 31#usize q13
  let q14 ← Array.index_usize openings.xor12_z 10#usize
  Array.update range5 32#usize q14

private theorem index_usize_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

/-- The candidate's real reconstruction wrappers and writes at indices 30–32
all succeed for canonical opening/range inputs. -/
theorem generated_tail_execution
    (openings : Openings) (range3 : Array QM 33#usize)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z)
    (hrange3 : CanonicalArray range3) :
    ∃ q5 q6 q7 q8 q9 q10 reconstructed q11 q12 q13 q14
      range4 range5 range6,
      AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
        openings.z = .ok q5 ∧ Canonical q5 ∧
      AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
        openings.succ_z = .ok q6 ∧ Canonical q6 ∧
      field.QM31.mul_m31 q6 scale10 = .ok q7 ∧ Canonical q7 ∧
      field.QM31.add q5 q7 = .ok q8 ∧ Canonical q8 ∧
      AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
        openings.xor12_z = .ok q9 ∧ Canonical q9 ∧
      field.QM31.mul_m31 q9 scale20 = .ok q10 ∧ Canonical q10 ∧
      field.QM31.add q8 q10 = .ok reconstructed ∧ Canonical reconstructed ∧
      Array.index_usize openings.z 10#usize = .ok q11 ∧ Canonical q11 ∧
      field.QM31.sub q11 reconstructed = .ok q12 ∧ Canonical q12 ∧
      Array.update range3 30#usize q12 = .ok range4 ∧
      Array.index_usize openings.succ_z 10#usize = .ok q13 ∧ Canonical q13 ∧
      Array.update range4 31#usize q13 = .ok range5 ∧
      Array.index_usize openings.xor12_z 10#usize = .ok q14 ∧ Canonical q14 ∧
      Array.update range5 32#usize q14 = .ok range6 ∧ CanonicalArray range6 ∧
      (1#u32 <<< 10#i32 : Result U32) = .ok scale10 ∧
      (1#u32 <<< 20#i32 : Result U32) = .ok scale20 ∧
      decode q12 = decode q11 -
        (reconstructModel openings.z +
          reconstructModel openings.succ_z *
            AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale10 +
          reconstructModel openings.xor12_z *
            AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale20) ∧
      tailConstruction openings range3 = .ok range6 := by
  obtain ⟨q5, hq5, hq5can, hq5dec⟩ :=
    AspisR1.SelectorReconstructIndexedSource.reconstruct_10_success openings.z hopenZ
  obtain ⟨q6, hq6, hq6can, hq6dec⟩ :=
    AspisR1.SelectorReconstructIndexedSource.reconstruct_10_success openings.succ_z hopenSucc
  obtain ⟨q9, hq9, hq9can, hq9dec⟩ :=
    AspisR1.SelectorReconstructIndexedSource.reconstruct_10_success openings.xor12_z hopenXor
  obtain ⟨q7, hq7, hq7can, hq7dec⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact q6 scale10
  obtain ⟨q8, hq8, hq8can, hq8dec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q5 q7 hq5can hq7can
  obtain ⟨q10, hq10, hq10can, hq10dec⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact q9 scale20
  obtain ⟨reconstructed, hrec, hreccan, hrecdec⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q8 q10 hq8can hq10can
  have hread11 : Array.index_usize openings.z 10#usize =
      .ok (openings.z.val[10]'(by simpa [openings.z.property] using
        (by scalar_tac : (10#usize).val < 16))) :=
    index_usize_ok openings.z 10#usize (by scalar_tac)
  have hq11can : Canonical (openings.z.val[10]'(by
      simpa [openings.z.property] using (by scalar_tac : (10#usize).val < 16))) :=
    hopenZ ⟨10, by simpa [openings.z.property] using
      (by scalar_tac : (10#usize).val < 16)⟩
  let q11 := openings.z.val[10]'(by
    simpa [openings.z.property] using (by scalar_tac : (10#usize).val < 16))
  have hread11' : Array.index_usize openings.z 10#usize = .ok q11 := by
    simpa [q11] using hread11
  obtain ⟨q12, hq12, hq12can, hq12dec⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact q11 reconstructed hq11can hreccan
  obtain ⟨range4, hupdate30, _hset30⟩ := WP.spec_imp_exists
    (Array.update_spec range3 30#usize q12 (by scalar_tac))
  have hread13 : Array.index_usize openings.succ_z 10#usize =
      .ok (openings.succ_z.val[10]'(by simpa [openings.succ_z.property] using
        (by scalar_tac : (10#usize).val < 16))) :=
    index_usize_ok openings.succ_z 10#usize (by scalar_tac)
  have hq13can : Canonical (openings.succ_z.val[10]'(by
      simpa [openings.succ_z.property] using (by scalar_tac : (10#usize).val < 16))) :=
    hopenSucc ⟨10, by simpa [openings.succ_z.property] using
      (by scalar_tac : (10#usize).val < 16)⟩
  let q13 := openings.succ_z.val[10]'(by
    simpa [openings.succ_z.property] using (by scalar_tac : (10#usize).val < 16))
  have hread13' : Array.index_usize openings.succ_z 10#usize = .ok q13 := by
    simpa [q13] using hread13
  obtain ⟨range5, hupdate31, _hset31⟩ := WP.spec_imp_exists
    (Array.update_spec range4 31#usize q13 (by scalar_tac))
  have hread14 : Array.index_usize openings.xor12_z 10#usize =
      .ok (openings.xor12_z.val[10]'(by simpa [openings.xor12_z.property] using
        (by scalar_tac : (10#usize).val < 16))) :=
    index_usize_ok openings.xor12_z 10#usize (by scalar_tac)
  have hq14can : Canonical (openings.xor12_z.val[10]'(by
      simpa [openings.xor12_z.property] using (by scalar_tac : (10#usize).val < 16))) :=
    hopenXor ⟨10, by simpa [openings.xor12_z.property] using
      (by scalar_tac : (10#usize).val < 16)⟩
  let q14 := openings.xor12_z.val[10]'(by
    simpa [openings.xor12_z.property] using (by scalar_tac : (10#usize).val < 16))
  have hread14' : Array.index_usize openings.xor12_z 10#usize = .ok q14 := by
    simpa [q14] using hread14
  obtain ⟨range6, hupdate32, _hset32⟩ := WP.spec_imp_exists
    (Array.update_spec range5 32#usize q14 (by scalar_tac))
  have hrange6 : CanonicalArray range6 :=
    AspisR1.SelectorValueLaneTailWritesCanonical.tail_three_updates_canonical
      openings range3 range4 range5 range6 q12 q13 q14 hopenSucc hopenXor
      hrange3 hq12can hupdate30 hread13' hupdate31 hread14' hupdate32
  have hq5dec' : decode q5 = reconstructModel openings.z := by
    change decode q5 = reconstructModel openings.z at hq5dec
    exact hq5dec
  have hq6dec' : decode q6 = reconstructModel openings.succ_z := by
    change decode q6 = reconstructModel openings.succ_z at hq6dec
    exact hq6dec
  have hq9dec' : decode q9 = reconstructModel openings.xor12_z := by
    change decode q9 = reconstructModel openings.xor12_z at hq9dec
    exact hq9dec
  have hq12dec' : decode q12 = decode q11 - decode reconstructed := by
    change decode q12 = decode q11 - decode reconstructed at hq12dec
    exact hq12dec
  have hrecdec' : decode reconstructed = decode q8 + decode q10 := by
    change decode reconstructed = decode q8 + decode q10 at hrecdec
    exact hrecdec
  have hq8dec' : decode q8 = decode q5 + decode q7 := by
    change decode q8 = decode q5 + decode q7 at hq8dec
    exact hq8dec
  have hq7dec' : decode q7 = decode q6 *
      AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale10 := by
    change decode q7 = decode q6 *
      AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale10 at hq7dec
    exact hq7dec
  have hq10dec' : decode q10 = decode q9 *
      AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale20 := by
    change decode q10 = decode q9 *
      AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale20 at hq10dec
    exact hq10dec
  have hvalue : decode q12 = decode q11 - (decode q5 +
      (decode q6 * AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale10) +
      decode q9 * AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale20) := by
    rw [hq12dec', hrecdec', hq8dec', hq7dec', hq10dec']
  have hq7run : field.QM31.mul_m31 q6
      AspisR1.SelectorValueLaneTailConstants.scale10 = .ok q7 := by
    change field.QM31.mul_m31 q6 scale10 = .ok q7
    exact hq7
  have hq8run : field.QM31.add q5 q7 = .ok q8 := hq8
  have hq10run : field.QM31.mul_m31 q9
      AspisR1.SelectorValueLaneTailConstants.scale20 = .ok q10 := by
    change field.QM31.mul_m31 q9 scale20 = .ok q10
    exact hq10
  have hrecrun : field.QM31.add q8 q10 = .ok reconstructed := hrec
  have hq12run : field.QM31.sub q11 reconstructed = .ok q12 := hq12
  have htail : tailConstruction openings range3 = .ok range6 := by
    unfold tailConstruction
    simp only [hq5, hq6,
      AspisR1.SelectorValueLaneTailConstants.shift10_success, hq7run, hq8run,
      hq9, AspisR1.SelectorValueLaneTailConstants.shift20_success, hq10run,
      hrecrun, hread11', hq12run, hupdate30, hread13', hupdate31, hread14',
      hupdate32, bind_tc_ok]
  refine ⟨q5, q6, q7, q8, q9, q10, reconstructed, q11, q12, q13, q14,
    range4, range5, range6, hq5, hq5can, hq6, hq6can, hq7, hq7can,
    hq8, hq8can, hq9, hq9can, hq10, hq10can, hrec, hreccan,
    hread11', hq11can, hq12, hq12can, hupdate30, hread13', hq13can,
    hupdate31, hread14', hq14can, hupdate32, hrange6,
    AspisR1.SelectorValueLaneTailConstants.shift10_success,
    AspisR1.SelectorValueLaneTailConstants.shift20_success, ?_, htail⟩
  rw [hvalue, hq5dec', hq6dec', hq9dec']

#print axioms generated_tail_execution
end
end AspisR1.SelectorValueLaneTailExecution
