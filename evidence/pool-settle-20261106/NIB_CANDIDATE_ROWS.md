# ADDED-PENDING-LEAD candidates (unused)

These are missing source-realization packets, not adopted trust. No theorem
uses a candidate as an axiom. RuntimeCpiReadonlyEntry7 remains PENDING and unused.

* **NIB-P1 — projected register continuity / same emission.** On the actual
  accepted Pool invocation `i` and far-side verifier emission of `s`, with the
  selected program `k`, prove the actual get-return-data prestate's return-register
  projection is `runtime.write (context i) k (S2K.ResultPayload.bytes s).val`.
  In addition to no intervening CPI, establish no intervening set/clear at this
  cut and the actual write-to-projection association. RuntimeReturnData and
  RuntimeReturnDataClear give their respective value laws, not native call
  provenance. Expected instantiation is exactly the `noInterveningCpi` binder
  printed in NIB_HYPOTHESES.md. Owner NHP successors + NHT/NHV/NHY. Do not assume
  generic CPI readonly entry or full-heap equality.
* **NIB-P2 — actual validation dictionary.** For the SAME reached request,
  master/checkpoint/lane/account keys and output_lane, identify `validate r`
  with the full Result of frozen pair_forest.rs::validate_authenticated_terminal_result_v1
  on those inputs and `r`, including actual ProgramError conversion. Supply
  `checked` from that actual call. S's terminal validator and emitted statement
  are not the Pool helper's reconstructed-statement identity. Owner NHP successors.
* **NIB-P3 — actual lane dictionary.** Identify `lane r` with frozen
  pair_forest.rs::next_lane_image_box_v1 on the SAME pre-lane and `r`; supply the
  actual image and `advanced`, including full Result/allocator interpretation.
  Owner NHP successors. Neither valid statement nor return-data read ensures
  that the actual lane is current or its image encoder succeeds.
* **NIB-P4 — production settlement continuation.** After P2/P3 at the SAME
  authenticated result, prove the native continuation's actual lane/page/marker
  borrows, optional withdrawal CPI and balance check, lane_data copy from image,
  correct page branch, marker_data copy from ready_marker, ASR8 return and guard
  cleanup with exact modifies/frame. The desired poststate is the source-order
  composition of these concrete effects on that prestate. NGK_NFR_ModelJoin
  concludes only `(image,ASR8)` plus `[validate,lane,encode]`; its statement does
  not mention any account heap or borrow counter. NFV's existing cuts are
  post-admission helper cuts; they do not contain this native continuation.
  Owner NHP successors / lead allocation. This is a slice-boundary finding,
  not a request for a new runtime success assumption.

Disposition: full POOL.read_to_settlement is OPEN. Model subtheorem is
PROVED-conditional. No candidate adopted, no row promoted, no security-scope change.
