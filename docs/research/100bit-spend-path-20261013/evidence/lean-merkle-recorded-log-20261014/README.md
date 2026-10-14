# Focused recorded-byte-log checkpoint

Base revision: `3c8e4eb428875e27bf3a061acf2329b61a9d1a59`.
The source manifest pins all eleven current sources and their successful
focused NUC receipts. The final combined target is
`R1MerkleRecordedLogCheckpoint-checkpoint-a`: exit 0, wall time 0.74 s,
peak RSS 1,797,808 KiB, zero swap, cgroup 4G/6G/0, with 29 axiom reports.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in successful
audits; no proof-placeholder axiom is present.

The bundle preserves 29 attempts: 17 failed, 11 selected final, and one
redundant green attempt. FirstHit attempt c accidentally repeated unchanged
green attempt b without a required reason. Both records are retained; b is
the selected first green result. The duplicate does not count as additional
verification. The 59 successful audit lines comprise 29 component lines,
29 checkpoint lines, and the redundant FirstHit line.

Every attempt includes its exact precompile source snapshot, both hash
sidecars, receipt, compiler output, and time log. The root audit checked
all hashes, receipt/time consistency, zero swap and explicit resource caps,
the eleven current-source matches, all archive members, runner pins, and
the fourteen unchanged runtime source fingerprints. The parser inventory
has a separate fourteen-source hash check recorded by the root.

Compiled objects are retained only in `objects/merkle-recorded-log-objects.tar.gz`,
SHA-256 `4bcbe934a8bcfb941fd472921cd9cde58adc41a8a99b92463bae10aa6dde99df`.
The pinned-cache Lean toolchain and runner are captured in `runner/`.
`ROOT-VALIDATION.json` records the independent local evidence audit;
`SHA256SUMS` seals the bundle files.

This is a focused component checkpoint, not a fresh build of the historical
manifest or a complete security certificate. Exact theorem scope and open
interfaces, including canonical bounded-address/byte-log correspondence,
are documented in [MERKLE-RECORDED-LOG.md](../../MERKLE-RECORDED-LOG.md).
