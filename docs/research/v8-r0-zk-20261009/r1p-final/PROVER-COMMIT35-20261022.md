# Prover commitment continuation 35

Target not yet established. D146 statement domain; D143 published-data scope,
excluding timing and other side channels. Intended trust list: inherited P7,
TrustedStd (unchanged), and D147 E1: successful OS RNG draws are uniform and
independent. E1 is a named environment hypothesis, not a Lean axiom.

Actual base: `6b5544772`; branch `codex/cx-prover-commit35-20261022`.
Env J9100–J9199 follows part 34 J9095. No shipped source change planned.

## Stages

1. Byte-blind adversarial schedule and retained reservation state: in progress.
2. Native failure-path/source control certification: pending.
3. Complete native simulator publication: pending.
4. Source-to-FSExperiments observation conversion: pending.
5. Concrete WholeRunJoins and endpoint: pending.

No premise deletion or completed endpoint is claimed by this setup checkpoint.

## Stage 1 checkpoint

`ProverCommitEnvironment35` (J9102) implements the byte-blind schedule,
including Unix directory open. `ask_blind` excludes private ledger/coin state
from schedule decisions. `create_retained` retains a created nonce on every
write/fsync outcome. `fail_closed` and `failure_replay` prove the environment
prefix returns only the same error, independent of witness and arbitrary
successful continuations, with the complete resulting private state retained.
This is a model theorem, pending the extracted/native callee bridge.

The schedule's arguments contain only index, kind and previous statuses; RNG
bytes and all three file payloads are excluded by construction. E1 separately
specifies conditional uniformity of each successful 96-byte draw for every
prior context. No OS/fs failure probability or new TrustedStd field is added.

J9100–J9101 are rejected proof drafts, preserved verbatim. J9102 exits 0,
2.48 s, peak RSS 4,174,784 KiB, zero swaps; all printed axioms are subsets of
[propext, Classical.choice, Quot.sound]. Receipts and source overlays are in
`evidence/prover-commit35-20261022/lean`.

Native checks substitute byte-blind OS primitives and downstream arithmetic;
they certify control, not the standard library, OS law or field arithmetic.
The reservation/create/write/fsync functions and the full reserve-before-build
method are copied verbatim and SHA-pinned. Initial extraction command v1 had
an obsolete --start-from name (exit 101); corrected v2 succeeds without source
or cap changes. This is a command correction, not a memory-pressure rerun.
