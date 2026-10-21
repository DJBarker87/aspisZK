# Checkpoint ABI continuation

Base ec56a3486, branch codex/cx-ckpt-abi2-20261021. Local commits only.

The current frozen source has not changed since the prior packet. Checkpoint
serialization lives in verifier.rs; candidate::tx1 writes after pending.finish,
and candidate::tx2_common resumes before the second query range. The model
`dV_frozen` contains neither checkpoint operation. Therefore a reference codec
roundtrip alone cannot discharge its surrounding driver identity.

Stages in progress: eliminate the Formatter dependency by proving that the
panic continuation is unreachable; exact per-function codec adoption with
explicit finite bounds; reached-state and driver composition. Every proof
receipt records revision, source and dependencies, command, exit, wall, peak
RSS, swap and complete axioms. Existing Lean and sibling modules are read-only.

## Stage 1 — panic continuation independence

`OraclePortCkptAbi2Unwrap` proves raw-read totality and exact immutable bytes
for every panic continuation, observational independence between any two
panic continuations, and totality of all saved-ten raw reads. This removes
the former unwrap-on-Ok premise for this explicit library model. It does not
assert that a concrete emitted Formatter instance is imported or identified.

Final local attempt 2: exit 0, wall 13.111534 seconds, peak RSS 2,240,479,232
bytes, zero swaps, source revision ec56a3486. All four axiom audits are
standard; the first failed attempt used a nonexistent scalar extensionality
lemma and is retained as failed evidence. No existing Lean module changed.
