import BatchedWeightsPushQueryGeneratedBridgeV12
import BatchedWeightsPushQueryGeneratedBridgeV9
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV13
open BatchedWeightsIndexedQueryLoopModelV2
open BatchedWeightsPushQueryGeneratedBridgeV9
open BatchedWeightsPushQueryGeneratedBridgeV12
abbrev Usize := BatchedWeightsIndexedQueryLoopModelV2.Usize
abbrev M := BatchedWeightsIndexedQueryLoopModelV2.M
abbrev Q := BatchedWeightsIndexedQueryLoopModelV2.Q
abbrev BW := BatchedWeightsIndexedQueryLoopModelV2.BW

theorem push_query_success_iff_model_success
    (basis : Array M 256#usize) (len : Usize) (state : BW) (power : Q)
    (hlen : len.val ≤ 256) (out : BW) :
    batched_weights.BatchedWeights.push_query state power basis len = .ok out ↔
      readPushQuery (Array.to_slice basis) (fun _ => power)
        (rangeCursorList len.val) state = .ok out := by
  constructor
  · exact push_query_actual_success_implies_model basis len state power hlen out
  · intro hmodel
    have hsource := push_query_success_refines_model basis len state power hlen out hmodel
    exact hsource

#print axioms push_query_success_iff_model_success
end BatchedWeightsPushQueryGeneratedBridgeV13
