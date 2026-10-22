# Prover commitment part 30

Branch `codex/cx-prover-commit30-20261022`; inherited source
`e78e2c022fddebb3d379963ea09efbca478664a7`. Target not yet established.
Env J 7868–7999 only, skipping existing receipts.

## Stage 1: isolate the native semantic callee

The first modular gate compares `SemanticTranscript::semantic` directly with
`semantic20::semantic`, before any record-vector lookup or semantic-array update.
It checks exact errors, state and row counter on rejection, three ordered hash
calls and their framing/answers on success, and identical pure sampler inputs
and call counts. The owned finite-field substitution is justified by the
retained `ProverCommitFields29.bounded_owned`; its zero-index and length
preconditions are asserted at the call site. The native validator is expanded.
This is a pending gate, not a verified contract or a completed native refinement.

All harness additions are external, cfg-only host adapters. No tracked file
under `crates/` or `programs/` has changed. Sources, resource receipts and
commands are retained in the part-30 evidence directory.

### Completed validation and callee gates

The native and owned validators are checked independently against the same
byte-level result. Each complete cell requires four little-endian low limbs
below `0x7fffffff` and sixteen zero high bytes. The result is exactly `Ok(())`
or `NonCanonical { row, value: first_failing_cell }`. The native one-cell gate
also covers ignored trailing suffixes. These checks use no field-validation
stubs. The owned gates expand `fields29::finite`; its substitution for
`fields20::validate` uses the unchanged J7866 bounded-owned theorem.

| Target / receipt | Exit | Wall s | GNU peak RSS KiB |
| --- | --- | --- | --- |
| native payload ≤63 / fields30-one-cell-v2 | 0 | 2.743 | 250068 |
| native payload 896 / fields30-exact896-v1 | 0 | 17.397 | 1093756 |
| owned payload 896 / fields30-owned896-v1 | 0 | 24.961 | 1322324 |
| owned payload 32 / fields30-owned32-v1 | 0 | 3.620 | 447928 |
| direct complete row 14 / semantic30-row14-v3 | 0 | 17.353 | 643676 |
| modular all semantic rows / semantic30-all-rows-modular-v1 | 0 | 19.535 | 648632 |

All use zero swap, the requested 6G/8G/0/64 scope and linker flags. Exact
commands, source revision and hashes, dependency fingerprint, scope peak and
raw logs are in `evidence/prover-commit30-20261022/rust-receipts.jsonl` and
`receipts/`. `#print axioms` is N/A for these Rust gates; no new Lean theorem
has yet been claimed.

The modular gate uses an arbitrary *common* validation result. At both call
sites it asserts the same row, payload length and every payload byte against
the original framed record. Byte equality is checked at a fresh arbitrary
in-range index: every index is covered, and the asserted positive payload
length ensures the index assumption never excludes an execution. The separate
native/owned validator gates above justify this congruence cut. The result is
not an assumed successful validation and may reject at any index. The sampler
likewise has an arbitrary common output, with identical input and call count
asserted. All three ordered hash calls are checked separately, including their
framing and answers. Exact semantic errors and the unchanged rejection state
are compared. The accepted scope is every row <25, arbitrary next-row counter,
transcript bytes and framed bytes of length ≤901.

The oversized initial recursive-fuel diagnostic and symbolic variable-length
28-cell diagnostic were stopped for shape review, without a verdict. Their
receipts are excluded. A duplicate-module installer error exited 101; the
installer was corrected and the exact failed source reconstructed against its
hash. None is represented as a proof or memory kill. `source-inventory.json`
checks 661 tracked files against the isolated host workspace: only the two
explicit cfg-only adapter files differ; every other source/configuration pin
matches. No tracked shipped source has changed.
