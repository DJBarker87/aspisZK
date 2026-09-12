# Source-connection continuation

Base `7e947e6a983d3e079ca67217bd9753351a398b7a`; isolated branch
`research/v8-completion-fs-extraction-20260911`. The base was pushed under the
user's renewed GitHub-publishing instruction. The full soundness goal remains
active; no global security number is claimed.

## New results

1. [Public affine correction](public-correction-agent.md): the two required
   original public weights now come from literal frozen mask bits and point-row
   computations, not caller-supplied weights. Same-word preparation produces the
   corrected scalar and preserves it across all later legal continuations.
2. [Positive query update](query-source-connection-20260912.md): the actual
   source adds the authenticated-value increment. A new constructor computes
   that increment and carries the resulting scalar through the three later
   compact responses. The old generic consumer's subtracted callback must not
   be identified with this positive increment. Existing discrepancy identities
   remain reusable; no protocol change or new probability bound was needed.
3. [Bounded sampler script connection](fs-script-agent.md): a causal script now
   provably reproduces each source-shaped transcript operation and the full
   bounded QM31 sampler, including result, digest, cache, tape index, log and
   exhaustion state. This connects the previously separate script freshness
   proof to the C1/challenges/C2 interpreter path. No caller-supplied freshness
   or script-correspondence certificate is required there.

## Validation

Focused leaves compiled first. The five-module `SourceConnectionAudit`
extension then compiled against the prior independently source-built NUC
artifacts, validating all eleven earlier source/artifact identities first.
No historical V8/Mathlib artifacts were substituted and unchanged prior source
modules were not rebuilt. The pinned Lean/Std distribution is reused.

`leanchecker --fresh -v SourceConnectionAudit` passed with exit 0, wall 63.40s,
peak RSS 983,380 KiB and swaps 0. The NUC job used `MemoryHigh=6G`,
`MemoryMax=8G`, `MemorySwapMax=0`, and a 600-second runtime cap. This is a replay
through the same Lean kernel, not independent external-kernel validation.
Printed promoted axioms are standard only. No retained theorem uses `sorry`.

Evidence: `results/v8-completion-fs-extraction-20260911/nuc-clean-20260912/connection.json`
and the six associated compiler/checker logs. Local source hashes and every log
hash were checked against that manifest after retrieval. Earlier manifests and
logs remain unchanged. `ConnectionBuild.py --work <certification-directory>`
reproduces the extension after `KernelBuild.py` and `FreshnessBuild.py` in an
appropriately capped Linux scope. It refuses existing extension artifacts/logs
or mismatched prior source/toolchain identities; use the recorded staged order.

The exact small-field controls check the public pair computation, failure and
nonvacuity cases, and the positive-versus-negative increment distinction.
They are not QM31 machine proofs, payment fixtures or measured security rates.
Agent source/premise review checked the query sign, indices and existing algebra
to reuse. Such review is distinct from independent cryptographic review.

## Remaining exact connection

These results still do not prove successful complete Rust verification produces
`SuccessfulAt` or a checked payment witness. In particular:

- Derive canonical authenticated quotient/fold values from the same records,
  roots, query ordering and checked geometry; feed them to the positive update.
- Connect the public functional, deferred image contribution, primal folds and
  terminal equation jointly, using the existing positive-update discrepancy
  lemmas rather than re-proving an isolated root bound.
- Connect all actual framed source challenges, public/runtime inputs and
  allowed adversarial continuations. The newly scripted sampler covers the
  source-shaped QM31 operation, not the later nonzero/OOD/query stages or the
  complete Rust execution. Initial digest preparation still needs its producer.
- Establish the random-tape law and permitted-access checked payment extraction,
  then compose probabilities with explicit retry/fork/time budgets. Fresh flags
  alone are not conditional uniformity. Algebraic recovery is not a witness.

No production changes, byte-format changes, CU measurements, privacy claim or
positive grinding credit. Body maximum remains 40,282 bytes. The next source
integration target is **same-body authenticated query values → positive scalar
and weight update → actual relation terminal**, together with the corrected
ordinary scalar—not another conditional numerical security estimate.
