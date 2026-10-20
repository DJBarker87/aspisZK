# Binary commitment model evidence

Verified on resume, 2026-10-20: **25/25 modules, 106 theorem audits**.
All current receipts exit 0; every theorem's `#print axioms` output is a
subset of `propext`, `Classical.choice`, and `Quot.sound`.
Successful module wall times total 114.23 seconds, maximum RSS is
3,032,498,176 bytes, and every process swap count is zero. These are focused
module runs using a pre-existing imported cache, not cold-build timings.

Branch `codex/r1-commit-model-20261019`, publication base `f9016d0a2`, resumed
from draft `d217103e1`. The handover `61e1a7928` had only a design skeleton
and tools. The previous draft's memory gate never allowed a Lean invocation;
`memory-preflight.json` is retained as historical evidence.

## Commands and receipts

The manifest lists the dependency order. Each module has `receipt.json`,
`lean.log` (full axiom output), and `time.log` (`/usr/bin/time -l`). Receipts
pin the exact command, source SHA, source parent revision, direct imported
object hashes, dependency fingerprint, output object hash/size, exit, wall,
peak RSS, process swaps, and system swap before/after. No objects are committed.

Local Lean 4.32.0 uses `-j1 -M4400 -DElab.async=false`, the exclusive shared
`/tmp/aspis-local-lean.lock.d` mkdir lock and a process gate, and own
`/tmp/r1-commit-model-20261019-objects`. The revised local rules supersede
the draft's obsolete 10 GiB free+inactive gate and flock wrapper.

From the worktree, the focused command is:

```sh
bash docs/research/100bit-spend-path-20261013/evidence/bin-commitment-model-20261019/tools/compile_local.sh MODULE
```

`tools/update_manifest.py --check` validates all source/output/import hashes,
complete theorem/axiom coverage, permitted axioms, and successful resource
receipts without repeating an unchanged Lean build. The final check passed.
The sequential successful compile pass covered every module in manifest
order; no unchanged successful module was rerun. Existing eight-way modules
and shared objects were untouched.

## Repairs

Five failed elaborations are preserved in the manifest's
`failed_attempt_receipts` and module `attempt-1/` directories:

- `BinGrammar`: ambiguous byte namespace and reserved identifier `public`.
- `BinMultiproof`: unfold symbolic slots when reducing dependent paths.
- `BinOpeningBinding`: qualify the byte type.
- `BinCanonicalCutWords`: qualify the byte type; also fixed proactively in
  `BinThreeCommitmentTypedOpening` before compiling it.
- `BinCompiledRunWordStability`: reduce local frame lets before rewriting cuts.

These repairs preserve the draft's mathematical statements. Failed logs
contain Lean's error-recovery `sorryAx`; successful receipts contain none.
No memory-limit failure occurred.

## Scope and obstruction

Proved: literal binary grammar and node/leaf/eight-way separation; symbolic
multiproof schedule and exact consumption; original-query path extraction
through dedup; prefix-only padded verification; same-index opening binding;
five-reader collision accounting `6 * Q² / 256³²`; causal raw-log recovery,
typed whole-word stability, and recording-compiler word stability.

The universal hash-input tag-disjointness request is false: verifier.rs:382
hashes arbitrary public bytes verbatim. Choose those bytes equal to a binary
node preimage. `BinGrammar.unrestricted_public_overlap` records the witness;
no collision or universal separation premise is assumed.

This is model-level evidence. `release_evidence: false` means no end-to-end
source/release claim; `model_verification_complete: true` records this packet's
completed compilation. R12/R13/R14 source extraction/refinement, actual batch
array loops, slot-byte/compact reconstruction, logging/frame provenance and
source freeze remain the separate source job. See
`../../design/BIN-COMMITMENT-MODEL-20261019.md` for the complete theorem map,
definition file:line provenance and remaining obligations.
