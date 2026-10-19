import BatchedWeightsPushQueryGeneratedBridgeV8
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsPushQueryGeneratedBridgeV9
open BatchedWeightsIndexedQueryLoopModelV2
open BatchedWeightsPushQueryGeneratedBridgeV4
open BatchedWeightsPushQueryGeneratedBridgeV8
abbrev Usize := BatchedWeightsIndexedQueryLoopModelV2.Usize
abbrev M := BatchedWeightsIndexedQueryLoopModelV2.M
abbrev Q := BatchedWeightsIndexedQueryLoopModelV2.Q
abbrev BW := BatchedWeightsIndexedQueryLoopModelV2.BW

/-- The generated source `push_query` including its single checked terms
increment agrees with V18's complete indexed query model whenever that model
succeeds. -/
theorem push_query_success_refines_model
    (basis : Array M 256#usize) (len : Usize) (state : BW) (power : Q)
    (hlen : len.val ≤ 256) (out : BW)
    (hmodel : readPushQuery (Array.to_slice basis) (fun _ => power)
      (rangeCursorList len.val) state = .ok out) :
    batched_weights.BatchedWeights.push_query state power basis len = .ok out := by
  unfold readPushQuery at hmodel
  cases hrows : readPushRows (Array.to_slice basis) (fun _ => power)
      (rangeCursorList len.val) state with
  | fail e => simp [hrows] at hmodel
  | div => simp [hrows] at hmodel
  | ok rows =>
      simp only [hrows, bind_tc_ok] at hmodel
      cases hterms : rows.terms + 1#usize with
      | fail e => simp [hterms] at hmodel
      | div => simp [hterms] at hmodel
      | ok nextTerms =>
          simp only [hterms, bind_tc_ok] at hmodel
          have hout : out = { rows with terms := nextTerms } := (Result.ok.inj hmodel).symm
          subst out
          have hloop := push_query_loop_refines_of_model_success
            basis len state power hlen rows hrows
          unfold batched_weights.BatchedWeights.push_query
          rw [hloop]
          simp only [bind_tc_ok]
          rw [hterms]
          rfl

#print axioms push_query_success_refines_model
end BatchedWeightsPushQueryGeneratedBridgeV9
