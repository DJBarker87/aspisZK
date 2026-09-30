import V7ProductionCallbacksR30DecoderCanonical

/-! Canonicality of the literal packed decoder's outer block loop. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30PackedDecoderCanonical

open V7ProductionCallbacksR30DecoderCanonical
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev Words (N : Std.Usize) := Array Std.U32 N
abbrev BlockState (N : Std.Usize) := Words N × Std.U32 × Std.Usize

def WordsCanonical {N : Std.Usize} (words : Words N) : Prop :=
  ∀ index, index < words.val.length →
    AspisAeneasCM31Multiplicative.CanonicalRawM31 words.val[index]!

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem add_values (left right output : Std.Usize)
    (run : left + right = (ok output : Result Std.Usize)) :
    output.val = left.val + right.val := by
  have spec := @UScalar.add_equiv UScalarTy.Usize left right
  rw [run] at spec
  exact spec.2.1

private theorem update_preserves_other {N : Std.Usize}
    (before after : Words N) (index : Std.Usize) (value : Std.U32)
    (run : Array.update before index value = ok after)
    (target : Nat) (different : index.val ≠ target) :
    after.val[target]! = before.val[target]! := by
  unfold Array.update at run
  split at run
  · cases run
  · cases run
    simp_lists

private theorem scanned_range_canonical {N : Std.Usize}
    (words : Words N) (start finish : Std.Usize) (slice : Slice Std.U32)
    (iter : ScanIter) (prior : Std.U32)
    (sliceRun : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U32))
      words { start := start, «end» := finish } = ok slice)
    (iterRun : SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      slice = ok iter)
    (scanRun : V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0
      iter prior = ok 0#u32) :
    prior = 0#u32 ∧ ∀ index, start.val ≤ index → index < finish.val →
      AspisAeneasCM31Multiplicative.CanonicalRawM31 words.val[index]! := by
  have scanner := successful_scanner_zero_canonical iter prior scanRun
  have iterExact : iter = ⟨slice, 0⟩ := by
    exact (Result.ok.inj iterRun).symm
  refine ⟨scanner.1, ?_⟩
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := start, «end» := finish } words.to_slice = ok slice at sliceRun
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at sliceRun
  split at sliceRun
  · have sliceExact := congrArg (fun s : Slice Std.U32 => s.val) (Result.ok.inj sliceRun)
    rename_i rangeBounds
    change start.val ≤ finish.val ∧ finish.val ≤ words.val.length at rangeBounds
    intro index lower upper
    have sliceLength : slice.val.length = finish.val - start.val := by
      rw [← sliceExact]
      simp_lists
      scalar_tac
    have canonical := scanner.2 (index - start.val)
      (by simp [iterExact]) (by simp [iterExact, Slice.length, sliceLength]; omega)
    simpa [iterExact, ← sliceExact,
      List.getElem!_slice start.val finish.val (index - start.val) words.val (by omega),
      Nat.add_sub_of_le lower] using canonical
  · cases sliceRun

private def blockBody {N : Std.Usize} (count : Std.Usize)
    (bytes : Slice Std.U8) (state : BlockState N) :
    Result (ControlFlow (BlockState N) (Words N × Std.U32)) :=
  V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0.body
    count bytes state.1 state.2.1 state.2.2

structure BlockContinuation {N : Std.Usize} (state next : BlockState N) : Type where
  base : Std.Usize
  finish : Std.Usize
  slice : Slice Std.U32
  iter : ScanIter
  finishValue : finish.val = base.val + 8
  outsideExact : ∀ index, index < base.val ∨ base.val + 8 ≤ index →
    next.1.val[index]! = state.1.val[index]!
  sliceSuccess : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U32))
    next.1 { start := base, «end» := finish } = ok slice
  iterSuccess : SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
    slice = ok iter
  scanSuccess : V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0_loop0
    iter state.2.1 = ok next.2.1

private theorem block_body_continuation_exposes
    {N : Std.Usize} (count : Std.Usize) (bytes : Slice Std.U8)
    (state next : BlockState N)
    (edge : blockBody count bytes state = ok (cont next)) :
    Nonempty (BlockContinuation state next) := by
  rcases state with ⟨output, prior, block⟩
  unfold blockBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0.body
    at edge
  split at edge
  ·
    rw [bind_eq_ok_iff] at edge
    obtain ⟨byte, byteRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨byteEnd, byteEndRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨chunk, chunkRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨base, baseRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read0, read0Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask0, mask0Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked0, masked0Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word0, word0Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output1, update0, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read1, read1Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨shift1, shift1Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask1, mask1Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked1, masked1Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index1, index1Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word1, word1Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output2, update1, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read2, read2Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨shift2, shift2Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask2, mask2Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked2, masked2Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index2, index2Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word2, word2Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output3, update2, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read3, read3Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨shift3, shift3Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask3, mask3Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked3, masked3Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index3, index3Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word3, word3Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output4, update3, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read4, read4Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨shift4, shift4Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask4, mask4Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked4, masked4Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index4, index4Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word4, word4Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output5, update4, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read5, read5Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨shift5, shift5Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask5, mask5Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked5, masked5Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index5, index5Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word5, word5Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output6, update5, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨read6, read6Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨shift6, shift6Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨mask6, mask6Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨masked6, masked6Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index6, index6Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word6, word6Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output7, update6, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨lastBytes, lastBytesRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨lastArrayResult, lastArrayResultRun, edge⟩ := edge
    cases lastArrayResult
    case Err error => simp [Bind.bind, Aeneas.Std.bind] at edge
    simp only at edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨lastArray, lastArrayRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨lastWord, lastWordRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨lastShift, lastShiftRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨index7, index7Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨word7, word7Run, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨output8, update7, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨finish, finishRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨slice, sliceRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨iter, iterRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨invalidAfter, scanRun, edge⟩ := edge
    rw [bind_eq_ok_iff] at edge
    obtain ⟨blockAfter, blockRun, edge⟩ := edge
    have stateExact := ControlFlow.cont.inj (Result.ok.inj edge)
    cases stateExact
    have index1Value := add_values base 1#usize index1 index1Run
    change index1.val = base.val + 1 at index1Value
    have index2Value := add_values base 2#usize index2 index2Run
    change index2.val = base.val + 2 at index2Value
    have index3Value := add_values base 3#usize index3 index3Run
    change index3.val = base.val + 3 at index3Value
    have index4Value := add_values base 4#usize index4 index4Run
    change index4.val = base.val + 4 at index4Value
    have index5Value := add_values base 5#usize index5 index5Run
    change index5.val = base.val + 5 at index5Value
    have index6Value := add_values base 6#usize index6 index6Run
    change index6.val = base.val + 6 at index6Value
    have index7Value := add_values base 7#usize index7 index7Run
    change index7.val = base.val + 7 at index7Value
    have finishValue := add_values base 8#usize finish finishRun
    change finish.val = base.val + 8 at finishValue
    exact ⟨{
      base := base
      finish := finish
      slice := slice
      iter := iter
      finishValue := finishValue
      outsideExact := by
        intro index outside
        calc
          output8.val[index]! = output7.val[index]! :=
            update_preserves_other output7 output8 index7 word7 update7
              index (by omega)
          _ = output6.val[index]! :=
            update_preserves_other output6 output7 index6 word6 update6
              index (by omega)
          _ = output5.val[index]! :=
            update_preserves_other output5 output6 index5 word5 update5
              index (by omega)
          _ = output4.val[index]! :=
            update_preserves_other output4 output5 index4 word4 update4
              index (by omega)
          _ = output3.val[index]! :=
            update_preserves_other output3 output4 index3 word3 update3
              index (by omega)
          _ = output2.val[index]! :=
            update_preserves_other output2 output3 index2 word2 update2
              index (by omega)
          _ = output1.val[index]! :=
            update_preserves_other output1 output2 index1 word1 update1
              index (by omega)
          _ = output.val[index]! :=
            update_preserves_other output output1 base word0 update0
              index (by omega)
      sliceSuccess := sliceRun
      iterSuccess := iterRun
      scanSuccess := scanRun
    }⟩
  · cases edge

private theorem block_continuation_zero_canonical
    {N : Std.Usize} {state next : BlockState N}
    (continuation : BlockContinuation state next)
    (nextZero : next.2.1 = 0#u32) :
    state.2.1 = 0#u32 ∧ (WordsCanonical state.1 → WordsCanonical next.1) := by
  have scanRun := continuation.scanSuccess
  rw [nextZero] at scanRun
  have scanned := scanned_range_canonical next.1 continuation.base continuation.finish
    continuation.slice continuation.iter state.2.1 continuation.sliceSuccess
    continuation.iterSuccess scanRun
  refine ⟨scanned.1, ?_⟩
  intro beforeCanonical index bound
  by_cases inside : continuation.base.val ≤ index ∧ index < continuation.base.val + 8
  · apply scanned.2 index inside.1
    rw [continuation.finishValue]
    exact inside.2
  · have outside : index < continuation.base.val ∨ continuation.base.val + 8 ≤ index := by
      omega
    rw [continuation.outsideExact index outside]
    apply beforeCanonical index
    have initialLength := state.1.property
    have nextLength := next.1.property
    omega

private theorem block_body_done_exact
    {N : Std.Usize} (count : Std.Usize) (bytes : Slice Std.U8)
    (state : BlockState N) (output : Words N × Std.U32)
    (edge : blockBody count bytes state = ok (done output)) :
    output = (state.1, state.2.1) := by
  unfold blockBody at edge
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0.body
    at edge
  split at edge
  · repeat' (rw [bind_eq_ok_iff] at edge; obtain ⟨_, _, edge⟩ := edge)
    split at edge
    · simp only at edge
      repeat' (rw [bind_eq_ok_iff] at edge; obtain ⟨_, _, edge⟩ := edge)
      cases edge
    · simp [Bind.bind, Aeneas.Std.bind] at edge
  · exact (ControlFlow.done.inj (Result.ok.inj edge)).symm

private theorem block_trace_zero_canonical
    {N : Std.Usize} {count : Std.Usize} {bytes : Slice Std.U8}
    {state : BlockState N} {output : Words N × Std.U32}
    (trace : ExactLoopTrace (blockBody count bytes) state output) :
    output.2 = 0#u32 → state.2.1 = 0#u32 ∧
      (WordsCanonical state.1 → WordsCanonical output.1) := by
  induction trace with
  | done edge =>
      intro zero
      have exactOutput := block_body_done_exact _ _ _ _ edge
      rw [exactOutput] at zero ⊢
      exact ⟨zero, fun canonical => canonical⟩
  | cont edge tail ih =>
      intro zero
      obtain ⟨nextZero, nextCanonical⟩ := ih zero
      obtain ⟨continuation⟩ := block_body_continuation_exposes _ _ _ _ edge
      obtain ⟨priorZero, preserves⟩ := block_continuation_zero_canonical continuation nextZero
      exact ⟨priorZero, fun canonical => nextCanonical (preserves canonical)⟩

theorem successful_packed_block_loop_canonical
    {N : Std.Usize} (count : Std.Usize) (bytes : Slice Std.U8)
    (initial output : Words N) (prior : Std.U32) (block : Std.Usize)
    (initialCanonical : WordsCanonical initial)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned_loop0
      count bytes initial prior block = ok (output, 0#u32)) :
    prior = 0#u32 ∧ WordsCanonical output := by
  have loopRun : loop (blockBody count bytes) (initial, prior, block) =
      ok (output, 0#u32) := run
  obtain ⟨trace⟩ := loop_success_yields_exact_trace (blockBody count bytes)
    (initial, prior, block) (output, 0#u32) loopRun
  have result := block_trace_zero_canonical trace rfl
  exact ⟨result.1, result.2 initialCanonical⟩

#print axioms successful_packed_block_loop_canonical

/-- Every successful source decoder result has canonical limbs. The proof is
generic in the array size and uses only the literal block and scanner traces. -/
theorem successful_packed_decoder_canonical
    (N : Std.Usize) (bytes : Slice Std.U8) (output : Words N)
    (run : V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned
      N bytes = ok (core.result.Result.Ok output)) : WordsCanonical output := by
  unfold V7ProductionCallbacksR29.aspis_core.v6_onefold.decode_packed_m31_eight_aligned
    at run
  split at run
  · cases run
  · rw [bind_eq_ok_iff] at run
    obtain ⟨remainder, remainderRun, run⟩ := run
    split at run
    · cases run
    · rw [bind_eq_ok_iff] at run
      obtain ⟨count, countRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨byteCount, byteCountRun, run⟩ := run
      split at run
      · cases run
      · simp only at run
        rw [bind_eq_ok_iff] at run
        obtain ⟨⟨decoded, invalid⟩, loopRun, run⟩ := run
        split at run
        · rename_i invalidZero
          have outputExact : decoded = output :=
            core.result.Result.Ok.inj (Result.ok.inj run)
          have initialCanonical : WordsCanonical (Array.repeat N 0#u32) := by
            intro index bound
            have indexBound : index < N.val := by simpa [Array.repeat] using bound
            simp [Array.repeat, List.getElem!_eq_getElem?_getD, indexBound,
              AspisAeneasCM31Multiplicative.CanonicalRawM31,
              AspisAeneasCM31Multiplicative.m31Modulus]
          change invalid = 0#u32 at invalidZero
          rw [invalidZero] at loopRun
          have canonical := successful_packed_block_loop_canonical count bytes
            (Array.repeat N 0#u32) decoded 0#u32 0#usize initialCanonical loopRun
          exact outputExact ▸ canonical.2
        · cases run

#print axioms successful_packed_decoder_canonical

end V7ProductionCallbacksR30PackedDecoderCanonical
