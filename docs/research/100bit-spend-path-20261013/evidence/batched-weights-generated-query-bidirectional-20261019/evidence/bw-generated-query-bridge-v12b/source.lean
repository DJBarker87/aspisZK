import BatchedWeightsPushQueryGeneratedBridgeV11
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV12
open BatchedWeightsIndexedQueryLoopModelV2
open BatchedWeightsPushQueryGeneratedBridgeV4
open BatchedWeightsPushQueryGeneratedBridgeV8
open BatchedWeightsPushQueryGeneratedBridgeV9
open BatchedWeightsPushQueryGeneratedBridgeV11
abbrev Usize := BatchedWeightsIndexedQueryLoopModelV2.Usize
abbrev M := BatchedWeightsIndexedQueryLoopModelV2.M
abbrev Q := BatchedWeightsIndexedQueryLoopModelV2.Q
abbrev BW := BatchedWeightsIndexedQueryLoopModelV2.BW
abbrev Range := core.ops.range.Range Usize

theorem push_query_actual_success_implies_model
    (basis : Array M 256#usize) (len : Usize) (state : BW) (power : Q)
    (hlen : len.val ≤ 256) (out : BW)
    (hactual : batched_weights.BatchedWeights.push_query state power basis len = .ok out) :
    readPushQuery (Array.to_slice basis) (fun _ => power)
      (rangeCursorList len.val) state = .ok out := by
  unfold batched_weights.BatchedWeights.push_query at hactual
  cases hloop : batched_weights.BatchedWeights.push_query_loop
      ({ start := 0#usize, «end» := len } : Range) state power basis with
  | fail err => simp [hloop] at hactual
  | div => simp [hloop] at hactual
  | ok rows =>
    simp only [hloop, bind_tc_ok] at hactual
    cases hterms : rows.terms + 1#usize with
    | fail err => simp [hterms] at hactual
    | div => simp [hterms] at hactual
    | ok nextTerms =>
      simp only [hterms, bind_tc_ok] at hactual
      have hrows := push_query_loop_actual_success_implies_model
        basis len state power hlen rows hloop
      unfold readPushQuery
      rw [hrows, bind_tc_ok, hterms, bind_tc_ok]
      have hOut : out = { rows with terms := nextTerms } :=
        ((Result.ok.inj hactual).symm)
      rw [hOut]

#print axioms push_query_actual_success_implies_model
end BatchedWeightsPushQueryGeneratedBridgeV12
