# Semantic finish to checked rounds and polynomial operation bridges

RawFinishCheckedSemanticRuns composes successful extracted FinishModel.finish with the exact RoundModel.rounds output and the existing ten-row CheckedRun. It retains row14 validation/decode/index-zero and all ten row15-24 record, boundary/comparator/value, alpha-update and transcript-transition facts. RoundModel.Boundaries and FinishModel.Boundaries remain explicit operation interfaces; this is not yet terminal acceptance-to-LiteralAcceptanceTerminal.Checks.

RawSemanticPolynomialOps proves the source-shaped seed-at-c0 additive fold equals p(0)+p(1), and reverse Horner equals p(alpha). RawSemanticArrayPolynomialOps lifts both identities to the exact Aeneas fixed Array K 28#usize representation.

RawExtractedSemanticQM31Ops reuses current_qm_add_exact and current_qm_mul_exact from ExtractedMaskQM31Exact. For canonical inputs, it proves successful Result-returning boundary and reverse-Horner folds project to those exact polynomial identities, including the 28-field array wrappers. This refines the selected arithmetic-probe QM31 owner; it does NOT identify that owner with AspisR1PublicPreparation.aspis_core.field.QM31 or instantiate the finish model's abstract operation boundaries. That owner/source correspondence remains open.

The recorded Rust formula source is r1_semantic.rs, SHA256 c66eba53bc3cdf801466455089d7189c02a0bec858f407a5fc9db35d10b17013. Its header explicitly labels it UNPROVED COST PROBE. The CU savings branch did not change that file, but it changed verifier arithmetic/weight bodies; the new optimized-body re-pins are separate pending work. No historical theorem is attributed to a changed body.

All four focused Lean 4.32 checks exited 0; times 13.56, 1.29, 4.11 and 3.11 seconds; maximum RSS 2,237,759,488, 1,621,819,392, 2,257,879,040 and 2,558,377,984 bytes; zero process swaps. All twelve axiom reports contain only propext, Classical.choice and Quot.sound. Exact commands, revisions, source/object/import hashes, raw logs and compiled objects are included. Earlier successful and failed operation-bridge attempts are retained in the original worker packet with their statuses.

These cached focused checks are working component evidence, not a clean unified-manifest release. Production acceptance refinement, owner/operation correspondence and the complete 100-bit private-spend proof remain open.
