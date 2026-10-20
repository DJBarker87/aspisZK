# Three retained CU equivalence proofs complete

All three selected optimizations now have checked source-bound equivalence against their exact parents, including consuming caller/context results. The parallel workers completed separate proof components; the final source/object/import audits pass together.

| Candidate | Retained measured saving | Evidence |
|---|---|---|
| 14: Libra factorization | 33,363–33,427 settlement CU | [LIBRA-CANDIDATE14-FINAL.md](LIBRA-CANDIDATE14-FINAL.md) |
| 2: Profiling removal | 24,193 combined CU (10,992 stage 1; 13,201 settlement) | [PROFILING-CANDIDATE2-FINAL.md](PROFILING-CANDIDATE2-FINAL.md) |
| 5: Canonical dot kernels | 22,890–22,916 combined CU | [CANONICAL-CANDIDATE5-COMPONENTS.md](CANONICAL-CANDIDATE5-COMPONENTS.md) |

The savings above are the existing matched measurements of retained production changes, not additional savings from this proof task. Production remains frozen at `39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. This task changed only proof sources, extraction fixtures, audit tooling and evidence. Unchanged runtime/SBF/codec regressions were not repeated.

Libra's final `CuSavingsLibraSourceOrigins.source_caller_context` consumes actual sampler/checkpoint-reader execution origins, the actual powers builders and low16 caller. Candidate 5's `CuSavingsCanonicalCandidate5Consumers` joins all five consuming contexts covering seven reachable push statements, deriving operand invariants from successful actual source producers. Profiling binds the actual observer dispatcher and callback through inverse-audited source factoring. No candidate-equivalence axiom is admitted.

These are source-equivalence results under the documented Rust/Charon/Aeneas, standard-library primitive, ownership, and source-layout/context boundaries. Profiling additionally assumes sufficient reference resources and returning SDK diagnostics, and projects diagnostic logs/private formatter allocations out of the relevant observations. They are not new whole-transaction extraction or compiled-program proofs. The production protocol, challenge schedule, proof/public/checkpoint encoding and cryptographic behavior are unchanged; no new soundness or privacy theorem is claimed here.

Every accepted Lean result has its exact command, source revision and hashes, features, exit, wall time, peak RSS, swap and `#print axioms` in selected receipts. Failed diagnostic attempts are retained but not selected as release evidence. Standard Lean axioms are recorded individually; candidate 5 additionally inherits `core.fmt.Formatter : Type` for unwrap diagnostics, an opaque runtime type rather than an equivalence law. Declaration re-pin inventories accompany each candidate.

The final Python audit ran the profiling, Wide arithmetic, Reader normalization, Libra source-origin, Libra candidate and canonical candidate checkers. All six exited zero. See [the exact audit receipt](THREE-CANDIDATES-FINAL-AUDIT.json); no new Lean or runtime build was launched for this final packaging check.

The side branch is `codex/r1-cu-savings-20261019`; the lead owns merging and archiving. No ELF, shared library, compiled Lean object or wallet key is included.

An independent parallel worker also checked publication completeness: all 130 candidate-5 source hashes match tracked index blobs, all 57 selected source/receipt hashes match, and the recursive 94-source local import closure has no missing file. This check made no edits and launched no Lean run.
