import BatchedWeightsIndexedQueryLoopModelV18
import BatchedWeightsPushQueryGeneratedBridgeV4
import AspisR1BatchedWeightsExtraction.Funs
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV8
open BatchedWeightsIndexedQueryLoopModelV2
open BatchedWeightsPushQueryGeneratedBridgeV4
abbrev Usize := BatchedWeightsIndexedQueryLoopModelV2.Usize
abbrev M := BatchedWeightsIndexedQueryLoopModelV2.M
abbrev Q := BatchedWeightsIndexedQueryLoopModelV2.Q
abbrev BW := BatchedWeightsIndexedQueryLoopModelV2.BW
abbrev Range := core.ops.range.Range Usize

theorem readPushRows_append (basis : Slice M) (powerAt : Usize → Q)
    (xs ys : List Usize) (state : BW) :
    readPushRows basis powerAt (xs ++ ys) state =
      (do let mid ← readPushRows basis powerAt xs state
          readPushRows basis powerAt ys mid) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih => simp [readPushRows, ih, bind_assoc]

/-- The extracted indexed loop and the V18 model have identical successful
results, assuming the model computation succeeds. The suffix-success invariant
makes each real body call total along the run. -/
theorem push_query_loop_refines_of_model_success
    (basis : Array M 256#usize) (len : Usize) (state : BW) (power : Q)
    (hlen : len.val ≤ 256) (out : BW)
    (hmodel : readPushRows (Array.to_slice basis) (fun _ => power)
      (rangeCursorList len.val) state = .ok out) :
    batched_weights.BatchedWeights.push_query_loop
      ({ start := 0#usize, «end» := len } : Range) state power basis = .ok out := by
  let initialIter : Range := { start := 0#usize, «end» := len }
  let allRows := rangeCursorList len.val
  let basisSlice := Array.to_slice basis
  let body := fun s : Range × BW =>
    batched_weights.BatchedWeights.push_query_loop.body power basis s.1 s.2
  have hwp : WP.spec (loop body (initialIter, state))
      (fun result : BW => readPushRows basisSlice (fun _ => power) allRows state = .ok result) := by
    refine loop.spec_decr_nat
      (fun s : Range × BW => len.val - s.1.start.val)
      (fun s => s.1.end.val = len.val ∧ s.1.start.val ≤ len.val ∧
        ∃ final : BW,
          readPushRows basisSlice (fun _ => power) (rangeCursorList s.1.start.val) state = .ok s.2 ∧
          readPushRows basisSlice (fun _ => power)
            (BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment s.1.start.val (len.val - s.1.start.val)) s.2 = .ok final ∧
          readPushRows basisSlice (fun _ => power) allRows state = .ok final)
      (fun result : BW => readPushRows basisSlice (fun _ => power) allRows state = .ok result)
      body (initialIter, state) ?_ ?_
    · rintro ⟨iter, acc⟩ ⟨hend, hstart, final, hprefix, hrest, hfinal⟩
      change iter.end.val = len.val at hend
      change iter.start.val ≤ len.val at hstart
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, hnext, hstartNext, hendNext, hroom⟩ :=
          AspisR1.OccupancyRangeTraversal.next_step iter hlt
        have hltLen : iter.start.val < len.val := by omega
        have hmax : Usize.max + 1 = 2^UScalarTy.Usize.numBits := Usize.max_succ_eq_pow
        have hcurBound : iter.start.val < 2^UScalarTy.Usize.numBits := by omega
        have hnextBound : iter.start.val + 1 < 2^UScalarTy.Usize.numBits := by omega
        have hcursor : (rangeCursor iter.start.val).val = iter.start.val :=
          rangeCursor_val iter.start.val hcurBound
        have hcursorNext : (rangeCursor (iter.start.val + 1)).val = iter.start.val + 1 :=
          rangeCursor_val (iter.start.val + 1) hnextBound
        have hlenSlice : basisSlice.length = 256 := by simp [basisSlice]
        have hindexBound : (rangeCursor iter.start.val).val < basisSlice.length := by
          rw [hcursor, hlenSlice]
          exact Nat.lt_of_lt_of_le hltLen hlen
        let basisValue := sliceCell basisSlice (rangeCursor iter.start.val) hindexBound
        have hread : Slice.index_usize basisSlice (rangeCursor iter.start.val) = .ok basisValue :=
          slice_read_actual basisSlice (rangeCursor iter.start.val) hindexBound
        have hreadArrayCursor : Array.index_usize basis (rangeCursor iter.start.val) = .ok basisValue := by
          rw [show Array.index_usize basis (rangeCursor iter.start.val) =
            Slice.index_usize (Array.to_slice basis) (rangeCursor iter.start.val) by rfl]
          exact hread
        have hindexEq : rangeCursor iter.start.val = iter.start := by
          apply UScalar.eq_of_val_eq
          rw [hcursor]
        have hreadArray : Array.index_usize basis iter.start = .ok basisValue := by
          rw [← hindexEq]
          exact hreadArrayCursor
        have hstartNextVal : iterNext.start.val = iter.start.val + 1 := hstartNext
        have hstartCursor : iterNext.start = rangeCursor (iter.start.val + 1) := by
          apply UScalar.eq_of_val_eq
          rw [hstartNextVal, hcursorNext]
        have htailLen : len.val - iter.start.val = (len.val - iter.start.val - 1) + 1 := by omega
        have hrestSplit : BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment iter.start.val (len.val - iter.start.val) =
            rangeCursor iter.start.val ::
              BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment (iter.start.val + 1) (len.val - iter.start.val - 1) := by
          calc
            _ = BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment iter.start.val
                ((len.val - iter.start.val - 1) + 1) := by congr 1
            _ = rangeCursor iter.start.val ::
                BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment
                  (iter.start.val + 1) (len.val - iter.start.val - 1) :=
              BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment_succ _ _
        have hrestEq : readPushRows basisSlice (fun _ => power)
            (BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment iter.start.val (len.val - iter.start.val)) acc = .ok final := hrest
        rw [hrestSplit] at hrestEq
        simp only [readPushRows, hread, bind_tc_ok] at hrestEq
        cases hp : batched_weights.BatchedWeights.push acc (rangeCursor iter.start.val)
            power basisValue with
        | ok accNext =>
          simp only [hp, bind_tc_ok] at hrestEq
          have htail : readPushRows basisSlice (fun _ => power)
              (BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment (iter.start.val + 1) (len.val - iter.start.val - 1)) accNext = .ok final := hrestEq
          have hpushAt : batched_weights.BatchedWeights.push acc iter.start power basisValue = .ok accNext := by
            rw [← hindexEq]
            exact hp
          have hprefixNext : readPushRows basisSlice (fun _ => power)
              (rangeCursorList iterNext.start.val) state = .ok accNext := by
            rw [show iterNext.start.val = iter.start.val + 1 from hstartNextVal]
            rw [BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorList_succ, readPushRows_append, hprefix]
            change readPushRows basisSlice (fun _ => power) [rangeCursor iter.start.val] acc = .ok accNext
            simp [readPushRows, hread, hp]
          have hrestNext : readPushRows basisSlice (fun _ => power)
              (BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment iterNext.start.val (len.val - iterNext.start.val)) accNext = .ok final := by
            rw [show iterNext.start.val = iter.start.val + 1 from hstartNextVal]
            have hlenEq : len.val - (iter.start.val + 1) = len.val - iter.start.val - 1 := by omega
            rw [hlenEq]
            exact htail
          have hbodyEval : body (iter, acc) = .ok (ControlFlow.cont (iterNext, accNext)) := by
            simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hpushAt, bind_tc_ok]
          rw [hbodyEval, WP.spec_ok]
          change (iterNext.end.val = len.val ∧ iterNext.start.val ≤ len.val ∧
              (∃ final' : BW,
                readPushRows basisSlice (fun _ => power) (rangeCursorList iterNext.start.val) state = .ok accNext ∧
                readPushRows basisSlice (fun _ => power)
                  (BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment iterNext.start.val (len.val - iterNext.start.val)) accNext = .ok final' ∧
                readPushRows basisSlice (fun _ => power) allRows state = .ok final')) ∧
              len.val - iterNext.start.val < len.val - iter.start.val
          refine ⟨⟨by rw [hendNext]; exact hend, by rw [hstartNextVal]; omega,
            ⟨final, hprefixNext, hrestNext, hfinal⟩⟩, by rw [hstartNextVal]; omega⟩
        | fail err =>
          simp [hp, bind_fail] at hrestEq
        | div =>
          simp [hp, bind_div] at hrestEq
      · have heq : iter.start.val = len.val := by omega
        have hdone : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) :=
          AspisR1.OccupancyRangeTraversal.next_done iter (by rw [hend]; omega)
        have hprefixAll : readPushRows basisSlice (fun _ => power) allRows state = .ok acc := by
          have hsplit := BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorList_split iter.start.val (len.val - iter.start.val)
          rw [show iter.start.val + (len.val - iter.start.val) = len.val by omega] at hsplit
          have hzero : len.val - iter.start.val = 0 := by omega
          rw [hzero] at hrest
          simp [BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment, readPushRows] at hrest
          have hacc : acc = final := hrest
          rw [← hacc] at hfinal
          exact hfinal
        have hbodyEval : body (iter, acc) = .ok (ControlFlow.done acc) := by
          simp [body, batched_weights.BatchedWeights.push_query_loop.body, hdone]
        rw [hbodyEval, WP.spec_ok]
        exact hprefixAll
    · refine ⟨by simp [initialIter], ?_, ?_⟩
      · change (0#usize).val ≤ len.val
        exact Nat.zero_le _
      · have hsplit := BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorList_split 0 len.val
        have hseg0 : rangeCursorList len.val = BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment 0 len.val := by
          simpa [rangeCursorList] using hsplit
        refine ⟨out, ?_, ?_, hmodel⟩
        · change readPushRows basisSlice (fun _ => power) (rangeCursorList 0) state = .ok state
          simp [rangeCursorList, readPushRows]
        · change readPushRows basisSlice (fun _ => power)
            (BatchedWeightsPushQueryGeneratedBridgeV4.rangeCursorSegment 0 len.val) state = .ok out
          rw [← hseg0]
          exact hmodel
  obtain ⟨result, hloop, hpost⟩ := WP.spec_imp_exists hwp
  have hres : result = out := by
    have heq : Result.ok result = Result.ok out := hpost.symm.trans hmodel
    exact Result.ok.inj heq
  have hactual : loop body (initialIter, state) = .ok result := hloop
  simpa [initialIter, body, batched_weights.BatchedWeights.push_query_loop] using
    (hactual.trans (congrArg Result.ok hres))

end BatchedWeightsPushQueryGeneratedBridgeV8
