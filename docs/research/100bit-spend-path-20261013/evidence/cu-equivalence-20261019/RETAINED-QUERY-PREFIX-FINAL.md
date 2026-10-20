# Actual query-prefix runtime and complete source callers

PASS. `CuSavingsRetainedQueryPrefixBinding` computationally instantiates `QueryCommon.queryPrefix` with exact index/query/authenticate/dots/fold factors. The source audit inverse reconstructs the entire frozen prefix and matches the historical common Rho prefix. Authentication retains its mark and rejects before dot work; all traces, folding checks and errors remain in the common suffix. The only gamma use is the actual dot kernel. No unchanged factor has mutable accumulator/pending input.

The concrete actual kernels are connected inside source `query_new.query_with_geometry`, `stage_query_new`, the complete emitted partial `stage_new` loop, and `tx_new.tx1_finish`. The loop theorem uses equal loop bodies, preserving divergence without a success or termination premise.

`CuSavingsRetainedQueryPrefixTx1.source_equivalence` proves complete actual source tx1 with optimized versus original dot runtime. It executes original parsing, marks, semantic verification, preparation and allocation first; only successful preparation derives gamma sampling/powers origins, then every actual stage query uses them. Failures, errors and divergence remain common computations. There is no successful-preparation/canonicality/equivalence premise.

`CuSavingsRetainedQueryPrefixTx2.tx2_equivalence` and `.tx2_authenticated_equivalence` prove both complete actual resumed transaction entrypoints with the concrete kernels. Actual strict checkpoint resume and actual powers computation supply all gamma origins internally. The authenticated parser and ordinary parser remain their original distinct source entrypoints.

`CuSavingsRetainedQueryPrefixGammaRho.source_tx1_equivalence` composes actual original gamma, original claim dot kernels, original rho, and original query dot kernels to their retained implementations in one complete tx1. It keeps the existing 64-bit and sufficient-allocation resource hypotheses; it introduces no new arithmetic/equivalence premise.

Nine new focused targets passed with max RSS 3,878,852 KiB, zero swap, wall 2.0–2.4 seconds per final target. Full commands, revisions, features, exit status, wall/RSS/swap and #print axioms are in the JSON/selected receipts. Axioms are standard three plus inherited `core.fmt.Formatter` debug runtime type. Diagnostic timeouts/stopped normalization attempts are preserved and unselected; replacement proofs use the already checked symbolic bind/branch skeleton and tiny callback equalities.

Boundary: existing audited source/compiler/runtime admission, exact source fission and coordinate-only nominal carriers. Unchanged index/auth/fold computations are shared verbatim; no new trusted interpreter or law field is introduced. This package closes the query replacements; the root final integration owns the other retained runtime components and complete bundle claim.

No production Rust change, binary, protocol change or new Rust re-pin. Existing candidate4/5/10 and gamma/rho inventories remain; new Lean declarations are enumerated in JSON.

Run `python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-retained-query-prefix-final.py --check`.
