import FJh_M31DotSevenOuter

/-! Complete actual seven-input QM31 by M31 scalar dot product, with no
execution-success or output-model premise. This is the internal-pair caller
boundary; arbitrary dot lengths are not claimed here. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotSevenExact
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (QM Exact Decode Canonical)
open AspisR1.FJh_M31DotReads
open AspisR1.FJh_M31DotSevenOuter (len_seven)

theorem source_success (weights : Slice QM) (values : Slice U32)
    (hwlen : weights.val.length = 7) (hvlen : values.val.length = 7)
    (hw : CanonicalWeights weights) (hv : CanonicalValues values) :
    ∃ out : QM, field.qm31_m31_dot weights values = .ok out ∧ Canonical out ∧
      Decode out = (List.ofFn (fun i : Fin 7 =>
        Decode (sliceCell weights i.val (by rw [hwlen]; exact i.isLt)) *
          ((sliceCell values i.val (by rw [hvlen]; exact i.isLt)).val : Exact))).foldl (·+·) 0 := by
  obtain ⟨raw,hrun,_,hraw⟩ := AspisR1.FJh_M31DotSevenOuter.source_success
    weights values hwlen hvlen hw hv
  obtain ⟨out,hfinish,hcanonical,hdecode⟩ := AspisR1.FJh_RawLimbReassembly.source_success raw
  have hfinish' : AspisR1.FJh_M31DotOuterSource.finish raw = .ok out := by
    rw [AspisR1.FJh_M31DotOuterSource.finish_source_eq]
    exact hfinish
  have hwlen' := len_seven weights hwlen
  have hvlen' := len_seven values hvlen
  have hlength : Slice.len weights = Slice.len values := hwlen'.trans hvlen'.symm
  have hlong : ¬ Slice.len weights ≤ 4#usize := by rw [hwlen']; decide
  refine ⟨out,?_,hcanonical,?_⟩
  · rw [AspisR1.FJh_M31DotOuterSource.source_long_eq weights values hlength hlong,
      AspisR1.FJh_M31DotChunkIterator.initial_source]
    simp only [hrun,hfinish',bind_tc_ok]
  · change Decode out = AspisR1.FJh_InternalLaneReassembly.rawDecode raw at hdecode
    exact hdecode.trans (hraw.trans
      (AspisR1.FJh_M31DotRemainingAlgebra.decode_remaining weights values 7
        (by omega) (by omega)))

#print axioms source_success
end AspisR1.FJh_M31DotSevenExact
