# R172 selected circle sampler

The actual selected source circle sampler now has exact finite execution and deterministic mathematical result/error/state proofs. End-to-end privacy and soundness remain open.

`R171SamplerCanonical.successful_canonical` proves every successful selected ordinary QM31 challenge under an arbitrary total byte function H has four canonical M31 coordinates. It derives this through the explicit R170 coordinate adapter and the already-proved R137 source sampler; no field-namespace equality is assumed.

`R172CircleSamplerExecution.body_factored` preserves the selected generated body, including its error mapping and early return. `loop_execution` proves equality with the finite source program `bounded` for every raw transcript/hash and every finite range. Both outer `Result.fail` and `Result.div` from ordinary sampling or circle conversion are preserved. Component sampling exhaustion returns `ChallengeSampleExhausted` immediately with its advanced transcript. A rejected conversion retries with its advanced transcript. Range exhaustion returns `ParameterSampleExhausted`. `three_attempts` specializes the actual unchanged source retry count to 3.

`bounded_exact` composes ordinary sampling with the proved canonical selected circle conversion to `SamplerCirclePolicy.pureMap`. `challenge_exact` proves the complete selected three-attempt circle result/error/state equality for arbitrary total H. Both conversion rejection reasons remain in the selected conversion theorem; their deliberate conversion to a retry follows the actual source body. The model retains stopping and the state reached at stopping. No freshness, randomness or probability law for H is asserted.

The exact source and successful focused records are in [the evidence manifest](evidence/r172-current-circle-sampler/manifest.json). The complete axiom output includes the inherited opaque `core.fmt.Formatter` type dependency used by source slice-error formatting. No new proof or execution axiom is introduced.

Verifier source and all security parameters are unchanged. Existing CU evidence and negative examples remain retained; no CU benchmark or regression suite was rerun.

The first remaining proposition is the current nonzero wrapper and then complete callback chronology. Whole trace equality, shared-oracle/seed/commitment/publication chronology, universal selected two-swap joint compatibility, a complete-view simulator and probability accounting remain open. Source-grounded extraction, quadratic folding, all soundness losses, and optimized-to-source acceptance also remain open. `RelationPrefixCorrespondence.BridgePremise.exact` is not claimed.
