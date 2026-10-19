# Finish-relation source candidate and checked equations

CANDIDATE, not adopted or a proof of the frozen source. Production code is unchanged.

The unchanged c8ea8dd49 `finish_relation` cannot currently be translated by the pinned Aeneas tool: shared-borrow replay fails while matching loop contexts. This candidate unrolls the one/two fold checks into a small scalar helper and moves the dot product into a helper over shared slices, with indexed iteration. Charon and Aeneas translate all three bodies. `verifier-candidate.patch` is the concrete proposed production-source delta; it has not been applied.

PROVED about the generated candidate, universally over explicit arithmetic/decoder/pairing/dot backends:

- Successful round checks imply successful reads of coefficients 0 and 4, their sum, claim-times-quarter, a false inequality guard and the polynomial output.
- Successful S2 finish implies both successful round calls, the same pairing call and final message, the same dot-product call, successful observer steps and both final guards.
- If the equality backend is faithful, those successful guards imply both fold equalities, pair equals the second claim, dot equals accumulator rhs, and next equals 22.

All five focused Lean targets passed on the NUC at -M4400 in 1 GiB high / 2 GiB max / swap0 scopes; proof axiom reports are standard. Exact sources, imports, compiler, commands, time/RSS/swap and object hashes are in the focused-extractor-proof-packet-v1 manifest and receipts. No binaries, template axioms or resource-option overrides are published. Raw generated bodies are pins; check-adapter.py verifies the elaboration delta.

OPEN before any source adoption or R14 closure: source/effect equivalence of the refactor, concrete backend instantiation (including pairing and dot arithmetic), dot-loop-to-sum correspondence, and CU remeasurement. The complete frozen tx2_common, resume and 12-query source refinement remain OPEN independently. This packet does not change the verifier source freeze, close R14, or establish 100-bit soundness.
