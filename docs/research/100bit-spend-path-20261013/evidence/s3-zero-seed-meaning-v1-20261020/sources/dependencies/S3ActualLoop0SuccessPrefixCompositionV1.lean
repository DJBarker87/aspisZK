import S3ActualLoop0SuccessReadbackV1
import S3ActualLoop0WholePrefix

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualLoop0SuccessReadback

private theorem bind_success_inv {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

noncomputable def successfulInput
    (bytes : Slice Std.U8) (low : Array field.WideExact 16#usize)
    (out : field.WideExact)
    (h : weights.s2_grouped_inactive_pair actualOperations bytes low = .ok out)
    (n : Nat) : AspisWideTower.WideExact :=
  if hn : n < 64 then
    let reads := grouped_pair_success_supplies_parser_reads bytes low out h n hn
    decode (Classical.choose (Classical.choose_spec reads))
  else 0

/-- Successful execution of the actual grouped-pair helper provides all 64
input-field reads required by the parser-backed loop-0 prefix theorem. The
input stream is defined from those exact successful callback outputs, so no
per-index callback-success or callback/value-map premise remains. The seed
meaning and canonicality are still explicit inputs. -/
theorem grouped_success_implies_prefix
    (bytes : Slice Std.U8) (low : Array field.WideExact 16#usize)
    (out : field.WideExact)
    (h : weights.s2_grouped_inactive_pair actualOperations bytes low = .ok out)
    (initialMeaning : Fin 12 → AspisWideTower.WideExact)
    (hinitMeaning : DecodedMeaning
      (Array.repeat 12#usize field.WideExact.ZERO)
      (PrefixMeaning (successfulInput bytes low out h) initialMeaning 0))
    (hinitCanonical : CanonicalAccumulatorArray
      (Array.repeat 12#usize field.WideExact.ZERO)) :
    ∃ result,
      weights.s2_grouped_inactive_pair_loop0 actualOperations
        { start := 0#usize, «end» := 64#usize } bytes
        (Array.repeat 12#usize field.WideExact.ZERO) = .ok result ∧
      DecodedMeaning result
        (PrefixMeaning (successfulInput bytes low out h) initialMeaning 64) ∧
      CanonicalAccumulatorArray result ∧
      (∀ n : Nat, n < 64 →
        ∃ (j : Std.Usize) (inputCoeff : field.WideExact)
          (raw : AspisR1RecordParser.field.wide_exact.WideExact)
          (start next finish : Std.Usize) (selected : Slice Std.U8),
          j.val = n ∧
          actualOperations.decodeField bytes j = .ok inputCoeff ∧
          AspisR1WeightsFieldCurrent.weights.field
            AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes j =
              .ok raw ∧
          (j * 32#usize : Result Usize) = .ok start ∧
          (j + 1#usize : Result Usize) = .ok next ∧
          (next * 32#usize : Result Usize) = .ok finish ∧
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
            { start := start, «end» := finish } = .ok selected ∧
          AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
            .ok (some raw)) := by
  unfold weights.s2_grouped_inactive_pair at h
  change (do
    let coefficients1 ← weights.s2_grouped_inactive_pair_loop0 actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize field.WideExact.ZERO)
    weights.s2_grouped_inactive_pair_loop1 actualOperations
      { start := 0#usize, «end» := 12#usize } low coefficients1
      field.WideExact.ZERO) = .ok out at h
  obtain ⟨coefficients1, hloop0, _hloop1⟩ := bind_success_inv
    (weights.s2_grouped_inactive_pair_loop0 actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize field.WideExact.ZERO))
    (fun coefficients1 => weights.s2_grouped_inactive_pair_loop1 actualOperations
      { start := 0#usize, «end» := 12#usize } low coefficients1
      field.WideExact.ZERO) out h
  have hfields : ∀ j : Std.Usize, j.val < 64 →
      ∃ x, decodeField bytes j = .ok x ∧
        decode x = successfulInput bytes low out h j.val := by
    intro j hj
    let reads := grouped_pair_success_supplies_parser_reads bytes low out h j.val hj
    let iter := Classical.choose reads
    let rest := Classical.choose_spec reads
    let inputCoeff := Classical.choose rest
    have hrest := Classical.choose_spec rest
    rcases hrest with ⟨raw, start, next, finish, selected,
      hidx, hdecode, hfield, hi, hn, hf, hs, hbytes⟩
    have hiter : Classical.choose reads = j := UScalar.eq_of_val_eq (by omega)
    have hdecodeAt : decodeField bytes j = .ok inputCoeff := by
      calc
        decodeField bytes j = decodeField bytes (Classical.choose reads) :=
          congrArg (fun q => decodeField bytes q) hiter.symm
        _ = .ok inputCoeff := hdecode
    refine ⟨inputCoeff, hdecodeAt, ?_⟩
    change decode inputCoeff = successfulInput bytes low out h j.val
    simp [successfulInput, hj, reads, rest, inputCoeff]
  have hprefix := actual_loop0_whole_prefix bytes
    (successfulInput bytes low out h) initialMeaning
    { start := 0#usize, «end» := 64#usize }
    (Array.repeat 12#usize field.WideExact.ZERO)
    (by scalar_tac) (by scalar_tac) hinitMeaning hinitCanonical hfields
  obtain ⟨result, hresult, hmeaning, hcanonical⟩ := hprefix
  have hreads := grouped_pair_success_supplies_parser_reads bytes low out h
  exact ⟨result, hresult, hmeaning, hcanonical, hreads⟩

#print axioms grouped_success_implies_prefix

end AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition
