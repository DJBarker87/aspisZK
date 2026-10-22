# Prover commitment continuation 43

Target not yet established. Worktree base: 5296bb1e509fdd32ec3cbb4fc70f640db071e7c7.
Branch: codex/cx-prover-commit43-20261022. No shipped sources changed.

## Stage 1: sixteen-candidate owner

The per-candidate native transition gate passes all 174 checks for arbitrary
64-byte draws, OS status, public nonce, retained bytes and every reachable
call/draw counter in the 0–15 candidate prefix. The extracted native body is
verbatim except for explicit stop/continue outcome wrapping: success and OS
error become terminal `Some` values; fall-through becomes `None`. The prior
verified zero-helper contract is reused as a verified substitution, not a
new trust item. No whole-loop harness runs. The Kani gate verifies bounded
native execution; its source mapping remains an external P6 boundary, not a
Lean proof about Rust syntax.

`ProverCommitNative43.range_run` proves the native `Range<usize>` denotation
by induction over the remaining candidates, preserving the complete
schedule/tape/state transition. `increment` proves no counter wrap before 16.
`generate_owner` identifies the zero-nonce guard and sixteen-step loop with
`AspisR1PublicNonce41.owner.generate`; `continuation` retains arbitrary
subsequent observations of both result and state. This closes the specific
part-42 native candidate/finite-loop verification gap, with the native
boundary and its independently proved Lean composition kept explicit.

J9494 is a rejected elaboration draft. J9495 accepts all five new theorems:
exit 0, wall 2.19 s, peak RSS 4,173,992 KiB, zero swaps, each axiom list
[propext, Classical.choice, Quot.sound]. Exact targets, source hashes,
dependency fingerprints, commands, source revision and full compiler output
are in `../../100bit-spend-path-20261013/evidence/prover-commit43-20261022/lean/`.
The native receipt and pinned inputs are beside them under `native/`,
`native-input-snapshots/`, `pins/` and `harness/native-source-check.json`.
No inherited Lean source/object is changed by the new module.

## Remaining stages

Native simulator publication, the literal source experiment conversion,
`shippedProverExperiment`, both WholeRunJoins and the endpoint without
RustProverRefinement remain open at this stage checkpoint. Trust list remains
P1, P7, TrustedStd, E1, E2. No nonce law or ledger cap is added. D143
observables and D146's announced source-representable statement domain are
retained. No release claim or endpoint premise removal is made here.
