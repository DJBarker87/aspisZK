# Oracle-verifier and Merkle checkpoint

Exact sampler-plus-terminal trace decomposition, read inclusions, Boolean-verifier specialization, and deterministic 32-byte path/salted-leaf binding.

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
| `R1Merkle32Leaf-a` | 0 | 0:00.74 | 1527016 | 0 | 5 |
| `R1Merkle32Path-a` | 0 | 0:00.97 | 1525952 | 0 | 8 |
| `R1OracleMerkleCheckpoint-a` | 0 | 0:00.73 | 1794772 | 0 | 22 |
| `R1OracleVerifier-oracle-verifier-g` | 0 | 0:01.02 | 1811320 | 0 | 5 |

Each final target passed in its own systemd scope with MemoryHigh=4G,
MemoryMax=6G, MemorySwapMax=0 and TasksMax=128. The pinned runner uses Lean
4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), one Lean worker,
a 5000 MB Lean memory threshold and a 900-second timeout. It checks active
reservations against a 50 GiB working budget, retaining at least 24 GiB for
the external group. The environment and runner snapshots are included.
Dependencies were reused from the pinned cache; this is not a cold replay.

The successful axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`, or no axioms. Failed logs may contain incomplete-declaration
reports and must not be treated as successful audits. All 10
attempt receipts are retained: 6 failed,
0 superseded successes, and
4 final successes.

## Evidence limitations and corrections

OracleVerifier attempts a through e have receipts, logs, time logs and
source hashes, but no exact source snapshots. The missing snapshots are
explicit in the manifest and ROOT-VALIDATION.json. Exact f and g snapshots
were recovered from the worker evidence only after matching their receipt
hashes. All final target snapshots are present and match current sources.

## Artifact integrity

The four final objects are stored in `objects/oracle-merkle-objects.tar.gz`,
SHA-256 `ab7ec074c282562c0c91e618d2078609df2a0c7c37c97a7c97addb641b4c0053`. The manifest records each
member's hash and size. Loose compiled objects are omitted. Final Lean
sources, receipt hashes, time logs, available attempt snapshots and runner
fingerprints are retained. `ROOT-VALIDATION.json` records root's independent
checks and the missing historical snapshots. `SHA256SUMS` seals every
other file in this directory, including this README.
