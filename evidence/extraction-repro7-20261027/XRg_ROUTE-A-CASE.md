# Route A decision input: opaque leaf count exceeds ten

Threshold reached after XRg_009: ten-leaf Aeneas fails canonical::Dot::push; adding exactly this body requires ELEVEN release leaves before any Types/Funs emission. Continue under the remaining 12-invocation budget; this is not a stop or approval request.

## Exact failures and provenance

Pinned Aeneas base revision b59d5188c082f704a418c7cb4e52ad69328002d1, extended Lean4.32 tree3be6820e84debbb8f2cc6b61abca478e98157bc7. Rebuilt binary SHA256 c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958. XRg_toolchain_base.json retains the historical38-file audit and its qualification; that historical binary has its own hash and is not called byte-identical to this rebuilt executable. No translator/library patch this round. Same release4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, built MIR/private-leaf-salts; all7978 source files rehashed on each Charon run.

- Shared-borrow collapse / abstraction-ID remapping: XRb check_values Not_found at InterpReduceCollapse1991; XRd prepared_claim also Not_found1991; XRf claims and XRg_002 decode_k internal error1880 (add_shared_borrows.update.update_avalues); XRg_005 validate_record_fields Not_found1991 in collapse_ctx_following_sequence1989–1992. These are loop-context translator failures, not mathematical counterexamples.
- InterpJoinCore.Distinct: XRb_006 verifier::echeck, “Could not find a matching abs in right environment,” through InterpLoopsFixedPoint. Inherited diagnostic evidence, not a new run or call-closed proof.
- Context mismatch: XRd_002 checkpoint, verifier.rs330:4–330:55, InterpJoin.ml2209, “Could not match the contexts.” Full contexts retained by predecessor.
- Borrow/value failures: XRc_001 expand_values compact.rs131–134, markers remaining after collapse; XRc_002 wide_view candidate.rs76–88, “There should be no bottoms in the value.” Current XRg_009 canonical::Dot::push fast_pairing.rs118:12–121:13, InterpBorrows.ml2731, simplify_dummy_values_useless_abs_aux.visit_ASharedLoan, through ReduceCollapse1645/1857 and Join1708. Full stack in XRg_009/stdout.log.
- Additional failure class this round: XRg_007 semantic_boundary r1_semantic.rs82–85, unsupported Arrow types at SymbolicToPureTypes570, after symbolic interpretation. This is distinct from borrow collapse.
- Selector limitation, not Aeneas semantics: Charon typed inherent-impl matcher is TODO/false. XRg_003 did not add decode_k; wildcard-single-method correction verified eight leaves in XRg_004. No Aeneas invocation on the ineffective-selector artifact.

## What an upgrade would change for D188

Recommendation for owner consideration: evaluate a separately pinned translator upgrade against minimal retained failures before extending the opaque boundary further. No upgrade is performed or authorized by this packet. More opacity adds P6 source-to-model obligations; it does not remove actual-top premises.

An upgrade changes the D188 extraction/toolchain pin, potentially the compatible Charon schema, Lean backend libraries, generated carriers/dictionaries, loop/borrow restorations and pure-function signatures. Re-emission must pin new binary/source/library hashes, check declaration closure and external mappings, compare old/new carriers/effects, re-establish each concrete source association and replay the selected final theorem dependency closure with standard-axiom audits and formatter reachability. Historical compiled objects are reusable only when source/dependency fingerprints remain valid. Do not attribute old tool evidence to new generated output by function name alone.

The source/feature/ELF pins stay frozen if only the translator changes; the source-to-ELF and generated-to-source association must still be checked on that same release. No automatic ELF rebuild or source adoption is implied. A tool upgrade is neither a protocol repair nor a cryptographic assumption. Frozen3, RuntimePersistence, game, failure event, metric and100-bit target remain unchanged. Target not yet established; premise delta0.

## Last exposed body

XRg_011 (eleven leaves) additionally fails the release circle_sample generated FnOnce closure. LLBC declaration sampler.rs122:78–127:5; Not_found InterpReduceCollapse1991 through eval_switch_with_join1407–1409. No narrower Rust diagnostic span. Adding only that closure requires twelve leaves; XRg_012 spends the last invocation on selector-only Charon and call-closure inventory. No translation of the resulting twelve-leaf LLBC is authorized beyond the twelve combined-invocation cap. Thus convergence is not established.
