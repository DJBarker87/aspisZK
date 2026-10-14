# Dual-pad and opening sampler checkpoint

Whole-word dual-pad correction under explicit subspace/preimage premises, its quadratic specialization, and independent-answer bounds for the four opening bad sets.

This is focused component evidence, not an end-to-end security, privacy,
source-refinement or release certificate. The source base is
`d5471c8c8a60ce4fe282610d5001c74b72486249`; exact per-target source SHA-256 values
are in `source-manifest.json`. Root reviewed the theorem statements and
premises, checked current-source hashes against final receipts, reconciled
the resource logs, verified object archive members, and audited axioms.
The 14 existing runtime source fingerprints are unchanged. No runtime
regression was repeated for these Lean-only changes.

| Exact target/attempt | Exit | Wall time | Peak RSS KiB | Swap | Axiom reports |
|---|---:|---|---:|---:|---:|
| `R1DualPadLift-a` | 0 | 0:01.40 | 2152392 | 0 | 3 |
| `R1DualPadWord-n` | 0 | 0:01.11 | 1809636 | 0 | 5 |
| `R1OpeningSamplerBound-opening-sampler-bound-f` | 0 | 0:01.66 | 3161512 | 0 | 6 |
| `R1PrivacyOpeningCheckpoint-a` | 0 | 0:01.29 | 3136260 | 0 | 14 |

Each final target passed in its own systemd scope with MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0 and TasksMax=128. The pinned runner uses Lean
4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), one Lean worker,
a 5000 MB Lean memory threshold and a 900-second timeout. It checks active
reservations against a 50 GiB working budget, retaining at least 24 GiB for
the external group. The environment and runner snapshots are included.
Dependencies were reused from the pinned cache; this is not a cold replay.

The successful axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`, or no axioms. Failed logs may contain incomplete-declaration
reports and must not be treated as successful audits. All 22
attempt receipts are retained: 17 failed,
1 superseded successes, and
4 final successes.

## Evidence limitations and corrections

OpeningSamplerBound attempts a through e have receipts, logs, time logs and
source hashes, but no exact source snapshots. The missing snapshots are
explicit in the manifest and ROOT-VALIDATION.json. Attempt d is a superseded
successful ordinary-gamma model; final f uses the nonzero modulo-P^8-1
sampler. No security claim relies on the superseded result.

DualPadWord attempt b aborted with a Lean memory exception after importing
all of Mathlib. GNU time records signal 6 and displays Exit status 0;
the shell and receipt correctly record 134 (=128+6). Root reconciled that
exception explicitly. The replacement uses narrow imports and a symbolic
word-sum identity, at the same cap; the failing job was not rerun unchanged
with a larger limit.

## Artifact integrity

The four final objects are stored in `objects/privacy-opening-objects.tar.gz`,
SHA-256 `cc53a5c0a69e145dd08dbbb84ce6353291ed9d792cc9932ad746af9c379bb55d`. The manifest records each
member's hash and size. Loose compiled objects are omitted. Final Lean
sources, receipt hashes, time logs, available attempt snapshots and runner
fingerprints are retained. `ROOT-VALIDATION.json` records root's independent
checks and the missing historical snapshots. `SHA256SUMS` seals every
other file in this directory, including this README.
