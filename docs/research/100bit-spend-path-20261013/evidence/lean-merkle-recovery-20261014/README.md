# Finite-table Merkle recovery checkpoint

This focused bundle checks finite node/leaf lookup and recovery alternatives,
literal oracle-program traces, partial-lane candidate bounds, a symbolic
parsed-target event bound, and the arbitrary-table D2 interface limitation.
It does not establish source correspondence, causal commitment binding,
efficient GS decoding, a privacy simulator, or end-to-end spend security.

Source base: `76cfcc9c9298223a7982e09519745e9378b39a30`. Exact source hashes and
object member hashes are in `source-manifest.json`. Root reviewed the final
source statements and proofs, checked all current sources against final
receipts, reconciled resource/time logs, audited axioms, and verified the
object archive and runner snapshots. All 14 existing runtime source pins
remain unchanged. No runtime regression was repeated for these Lean changes.

| Exact target/attempt | Exit | Wall time | Peak RSS KiB | Swap | Axiom reports |
|---|---:|---|---:|---:|---:|
| `R1D2TableBoundary-a` | 0 | 0:00.76 | 1816984 | 0 | 1 |
| `R1MerkleLeafRecovery-b` | 0 | 0:00.72 | 1531516 | 0 | 2 |
| `R1MerkleProgram-merkle-program-c` | 0 | 0:00.88 | 1810796 | 0 | 4 |
| `R1MerkleRecovery-b` | 0 | 0:00.67 | 1525236 | 0 | 2 |
| `R1MerkleRecoveryCheckpoint-checkpoint-a` | 0 | 0:01.21 | 3132492 | 0 | 22 |
| `R1MerkleTable-table-k` | 0 | 0:00.84 | 1531852 | 0 | 7 |
| `R1ParsedTargetsCollision-parsed-targets-collision-c` | 0 | 0:00.90 | 1812424 | 0 | 2 |
| `R1PartialJointList-e` | 0 | 0:01.45 | 3146860 | 0 | 4 |

All runs used the pinned Lean 4.32.0 cache
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), one worker, a 5000 MB Lean
threshold and a 900-second timeout. Each ran in a separate 4G MemoryHigh,
6G MemoryMax, zero-swap, TasksMax=128 systemd scope. The runner checked
active reservations against 50 GiB, retaining at least 24 GiB for the
external group. This is focused cached replay, not a cold release replay.

All successful axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`, or a subset. In particular the constructive digest equality,
lookup and walk helpers use only `propext` and `Quot.sound`. There are
58 successful reports including the combined
22-report checkpoint and superseded successes. Failed logs are retained
as failures and are not security evidence.

## Retained attempts and changes

All 28 attempts have exact source snapshots, receipt hashes, compiler hash
sidecars, snapshot hash sidecars, stdout logs and time logs. The manifest
classifies 17 failures, three superseded successes, and eight final
successes. No historical source snapshot is missing in this bundle.

The node-table draft `table-i` used classical equality; root required a
constructive 32-byte comparison. `table-j` supplied that comparison and
`table-k` gives it a named exported definition. The unchanged recovery source
was compiled again as `b` after this dependency change; `a` is superseded.
No unchanged whole-package regression was run. The partial-list projection
uses a local maxRecDepth of 8192 to accommodate a linter recursion issue;
it does not unfold a large recurrence or generated numerical certificate.

`compile-snapshot.sh` is the new precompile wrapper. It saves the source
before invoking the unchanged capped `compile-one.sh`, refuses to overwrite
an existing snapshot, and checks that the source did not change during the
run. Its manifest hash matches the committed local tools copy. The three
older runner/environment fingerprints match the previous checkpoint.

## Artifact integrity

The eight final objects are retained in
`objects/merkle-recovery-objects.tar.gz`, SHA-256
`70706e33413aba489fc04345eb95c028e53432de27919fbba02ccf9b37e67136`. The manifest records the size and
hash of every member; there are no loose object files. The independent
root audit is recorded in `ROOT-VALIDATION.json`. `SHA256SUMS` seals every
other file in this directory, including this README.
