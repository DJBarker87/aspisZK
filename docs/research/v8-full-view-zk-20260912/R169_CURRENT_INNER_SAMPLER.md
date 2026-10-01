# R169 current transcript and per-limb execution

The selected R156 source transcript primitives and complete four-limb QM31 sampler have exact deterministic execution proofs. This is a source correspondence milestone; end-to-end privacy and soundness remain open.

`R167TranscriptPrimitiveExecution` proves raw squeeze and absorb equality through explicit transcript representation maps. Every hash `Result.fail` and `Result.div` is preserved. Packed and long absorbs are both retained. For an arbitrary total byte function H, the state updates equal the existing exact frame model. This does not instantiate randomness or a shared-oracle distribution.

`R169InnerSamplerExecution.body_map` proves each selected source retry body exactly matches R137 after mapping the returned control state and final state. `loop_map` proves the full finite range execution for every raw limb, range, block, and word index. It uses induction on the remaining range length, with identical checked iterator steps and wrapping word reads. Short/invalid word reads and hash failures are retained. `eight_attempts_map` specializes both independently extracted retry constants to their actual unchanged value 8. There is no assumption equating namespaces.

The loop proof neither unfolds concrete callback claims nor changes verifier source or parameters. Existing CU evidence and negative examples remain intact. No CU or regression suite was rerun.

The complete axiom lists and focused command/resource results are in [the evidence manifest](evidence/r169-current-inner-sampler/manifest.json). R167 uses standard Lean foundational axioms only. R169 also exposes the existing opaque `core.fmt.Formatter` type dependency of source slice-error formatting; no new operational or correspondence axiom was added.

`R170LimbSamplerExecution.loop_map` also preserves the mutable four-limb iterator and deferred write-back functions. `challenge_map` proves the complete current raw QM31 challenge result/error/state equality; `challenge_exact` composes it with the existing exact model for any total H.

The first remaining proposition is the exact current three-attempt circle sampler and nonzero wrapper. The three-attempt circle sampling loop, complete callback trace, shared-oracle challenge law, full-view privacy, probability accounting, extraction and optimized-to-source acceptance remain open. No `BridgePremise.exact` is claimed.
