import BatchedWeightsPushQueryGeneratedBridgeV10
import AspisR1BatchedWeightsExtraction.Funs
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV11
open BatchedWeightsIndexedQueryLoopModelV2
open BatchedWeightsPushQueryGeneratedBridgeV4
open BatchedWeightsPushQueryGeneratedBridgeV8
open BatchedWeightsPushQueryGeneratedBridgeV10
abbrev Usize := BatchedWeightsIndexedQueryLoopModelV2.Usize
abbrev M := BatchedWeightsIndexedQueryLoopModelV2.M
abbrev Q := BatchedWeightsIndexedQueryLoopModelV2.Q
abbrev BW := BatchedWeightsIndexedQueryLoopModelV2.BW
abbrev Range := core.ops.range.Range Usize

theorem push_query_loop_actual_success_implies_model
    (basis : Array M 256#usize) (len : Usize) (state : BW) (power : Q)
    (hlen : len.val ≤ 256) (out : BW)
    (hactual : batched_weights.BatchedWeights.push_query_loop
      ({ start := 0#usize, «end» := len } : Range) state power basis = .ok out) :
    readPushRows (Array.to_slice basis) (fun _ => power)
      (rangeCursorList len.val) state = .ok out := by
  let initialIter : Range := { start := 0#usize, «end» := len }
  let basisSlice := Array.to_slice basis
  let body := fun s : Range × BW =>
    batched_weights.BatchedWeights.push_query_loop.body power basis s.1 s.2
  have hwp : WP.spec (loop body (initialIter, state))
      (fun result : BW => readPushRows basisSlice (fun _ => power)
        (rangeCursorList len.val) state = .ok result) := by
    refine loop.spec_decr_nat
      (fun s : Range × BW => len.val - s.1.start.val)
      (fun s => s.1.end.val = len.val ∧ s.1.start.val ≤ len.val ∧
        ∃ final : BW,
          readPushRows basisSlice (fun _ => power)
            (rangeCursorList s.1.start.val) state = .ok s.2 ∧
          loop body (s.1, s.2) = .ok final)
      (fun result : BW => readPushRows basisSlice (fun _ => power)
        (rangeCursorList len.val) state = .ok result)
      body (initialIter, state) ?_ ?_
    · rintro ⟨iter, acc⟩ ⟨hend, hstart, final, hprefix, hloop⟩
      change iter.end.val = len.val at hend
      change iter.start.val ≤ len.val at hstart
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, hnext, hstartNext, hendNext, hroom⟩ :=
          AspisR1.OccupancyRangeTraversal.next_step iter hlt
        have hltLen : iter.start.val < len.val := by omega
        have hmax : Usize.max + 1 = 2^UScalarTy.Usize.numBits := Usize.max_succ_eq_pow
        have hcurBound : iter.start.val < 2^UScalarTy.Usize.numBits := by omega
        have hnextBound : iter.start.val + 1 < 2^UScalarTy.Usize.numBits := by omega
        have hcursor : (rangeCursor iter.start.val).val = iter.start.val := by
          rw [rangeCursor_val iter.start.val hcurBound]
        have hcursorNext : (rangeCursor (iter.start.val + 1)).val = iterNext.start.val := by
          rw [rangeCursor_val (iter.start.val + 1) hnextBound, hstartNext]
        have hlenSlice : basisSlice.length = 256 := by simp [basisSlice]
        have hindexBound : (rangeCursor iter.start.val).val < basisSlice.length := by
          rw [rangeCursor_val iter.start.val hcurBound, hlenSlice]
          exact Nat.lt_of_lt_of_le hltLen hlen
        let basisValue := sliceCell basisSlice (rangeCursor iter.start.val) hindexBound
        have hreadSlice : Slice.index_usize basisSlice (rangeCursor iter.start.val) = .ok basisValue :=
          slice_read_actual basisSlice (rangeCursor iter.start.val) hindexBound
        have hreadArrayCursor : Array.index_usize basis (rangeCursor iter.start.val) = .ok basisValue := by
          rw [show Array.index_usize basis (rangeCursor iter.start.val) =
            Slice.index_usize (Array.to_slice basis) (rangeCursor iter.start.val) by rfl]
          exact hreadSlice
        have hiterCursor : rangeCursor iter.start.val = iter.start := by
          apply UScalar.eq_of_val_eq
          rw [rangeCursor_val iter.start.val hcurBound]
        have hreadArray : Array.index_usize basis iter.start = .ok basisValue := by
          rw [← hiterCursor]
          exact hreadArrayCursor
        rcases loop_success_cases body (iter, acc) final hloop with hdone | ⟨nextState, hbody, htail⟩
        · have hdoneRed := hdone
          cases hp : batched_weights.BatchedWeights.push acc iter.start power basisValue with
          | fail err => simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hp, bind_tc_ok] at hdoneRed
          | div => simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hp, bind_tc_ok] at hdoneRed
          | ok pushed => simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hp, bind_tc_ok] at hdoneRed
        · rcases nextState with ⟨iterActual, accActual⟩
          have hbodyRed := hbody
          cases hpush : batched_weights.BatchedWeights.push acc iter.start power basisValue with
          | fail err => simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hpush, bind_tc_ok] at hbodyRed
          | div => simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hpush, bind_tc_ok] at hbodyRed
          | ok pushed =>
            simp [body, batched_weights.BatchedWeights.push_query_loop.body,
              hnext, hreadArray, hpush, bind_tc_ok] at hbodyRed
            rcases hbodyRed with ⟨hiterEq, haccEq⟩
            subst iterActual
            subst accActual
            have htailNext : loop body (iterNext, pushed) = .ok final := htail
            have hbodyEval : body (iter, acc) = .ok (.cont (iterNext, pushed)) := by
              simp [body, batched_weights.BatchedWeights.push_query_loop.body,
                hnext, hreadArray, hpush, bind_tc_ok]
            have hrowModel : readPushRows basisSlice (fun _ => power)
                [rangeCursor iter.start.val] acc = .ok pushed := by
              simp only [readPushRows, hreadSlice, bind_tc_ok]
              have hpushCursor : batched_weights.BatchedWeights.push acc
                  (rangeCursor iter.start.val) power basisValue = .ok pushed := by
                simpa [hiterCursor] using hpush
              simp [hpushCursor]
            have hprefixNext : readPushRows basisSlice (fun _ => power)
                (rangeCursorList iterNext.start.val) state = .ok pushed := by
              rw [show iterNext.start.val = iter.start.val + 1 from hstartNext]
              rw [rangeCursorList_succ, readPushRows_append, hprefix]
              change readPushRows basisSlice (fun _ => power)
                [rangeCursor iter.start.val] acc = .ok pushed
              exact hrowModel
            rw [hbodyEval, WP.spec_ok]
            change (iterNext.end.val = len.val ∧ iterNext.start.val ≤ len.val ∧
              ∃ final' : BW,
                readPushRows basisSlice (fun _ => power)
                  (rangeCursorList iterNext.start.val) state = .ok pushed ∧
                loop body (iterNext, pushed) = .ok final') ∧
              len.val - iterNext.start.val < len.val - iter.start.val
            refine ⟨⟨by rw [hendNext]; exact hend, by rw [hstartNext]; omega,
              ⟨final, hprefixNext, htailNext⟩⟩, by rw [hstartNext]; omega⟩
      · have heq : iter.start.val = len.val := by omega
        have hdone : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (none, iter) :=
          AspisR1.OccupancyRangeTraversal.next_done iter (by rw [hend]; omega)
        rcases loop_success_cases body (iter, acc) final hloop with hdoneLoop | ⟨nextState, hbody, htail⟩
        · have hbodyEval : body (iter, acc) = .ok (.done acc) := by
            simp [body, batched_weights.BatchedWeights.push_query_loop.body, hdone]
          have hEq := hbodyEval.symm.trans hdoneLoop
          have hEq' : ControlFlow.done acc = ControlFlow.done final := Result.ok.inj hEq
          have hfinal : final = acc := by cases hEq'; rfl
          subst final
          have hprefixAll : readPushRows basisSlice (fun _ => power)
              (rangeCursorList len.val) state = .ok acc := by
            rw [← heq]
            exact hprefix
          rw [hbodyEval, WP.spec_ok]
          exact hprefixAll
        · have hbodyRed := hbody
          simp only [body, batched_weights.BatchedWeights.push_query_loop.body] at hbodyRed
          rw [hdone] at hbodyRed
          simp only [bind_tc_ok] at hbodyRed
          simp at hbodyRed
    · refine ⟨by simp [initialIter], ?_, ?_⟩
      · change (0#usize).val ≤ len.val
        exact Nat.zero_le _
      · refine ⟨out, ?_, ?_⟩
        · change readPushRows basisSlice (fun _ => power) (rangeCursorList 0) state = .ok state
          simp [rangeCursorList, readPushRows]
        · simpa [initialIter, body, batched_weights.BatchedWeights.push_query_loop] using hactual
  obtain ⟨result, hloop, hmodel⟩ := WP.spec_imp_exists hwp
  have hresult : result = out := Result.ok.inj (hloop.symm.trans hactual)
  simpa [hresult] using hmodel

#print axioms push_query_loop_actual_success_implies_model
end BatchedWeightsPushQueryGeneratedBridgeV11
