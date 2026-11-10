# The R1 proof package

This folder holds the part of the evidence for the current version that
fits on `main`. The full evidence, some 45 GB of Lean sources, compiled
objects, receipts and logs, stays on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch, and
nothing here replaces it. Each file was taken from a named commit on that
branch, given in the table, so any of them can be checked against the commit it
came from. The release target, 100-bit classical soundness per attempt for the
spend path that actually runs, is not yet established; what stands in the way
is in [`OPEN-GATES.md`](OPEN-GATES.md).

| File | What it is | Research commit |
| --- | --- | --- |
| [`SECURITY-CONTRACT.md`](SECURITY-CONTRACT.md) | The security contract the work is held to, with every amendment the owner has approved, followed by the amendment that made the adversary arbitrary and adaptive. | `07123926e88` |
| [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md) | The status document, which gives the theorem in prose and in Lean, every binder and retained hypothesis, the exact bound and its valid range, the trust it rests on, what it does not claim and what remains; | `cfa09f5e2c4` |
| [`TOP-THEOREM.md`](TOP-THEOREM.md) | The two top theorems as Lean prints them, with a plain reading of every part of each statement and the axiom and closure audit. | `07123926e88` |
| [`TAS_FinalB.lean`](TAS_FinalB.lean) | The Lean source that proves the two theorems, copied unchanged. | `07123926e88` |
| [`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json) | The full audit record of the final assembly, copied unchanged. | `07123926e88` |
| [`LEDGER-599.md`](LEDGER-599.md) | One line for each of the 599 verified statements, giving the Rust function, its domain and its root theorems, generated mechanically from the ledger. | `07123926e88` |
| [`NNN_LEDGER.json.xz`](NNN_LEDGER.json.xz) | The complete ledger, a compressed copy of 1.1 MB. | `07123926e88` |
| [`TRUST-INVENTORY.md`](TRUST-INVENTORY.md) | Every named trust row, the current table followed by the approved appendix, as it stood before the reconciliation of 10 November now in section 4 of the status document. | `07123926e88` |
| [`DEVNET-RUN.md`](DEVNET-RUN.md) | The two devnet runs, on 29 October and 10 November 2026, with the programs, ELF hashes and signatures, what settled and what was rejected. | `07123926e88` and `af8f9fd2f9d` |
| [`BUILD.md`](BUILD.md) | How the release ELF is built, the overflow-check setting it is built with, and the receipt showing it reproduced. | `07123926e88` |
| [`OPEN-GATES.md`](OPEN-GATES.md) | What remains between the assembled theorem and the claim, one paragraph for each item, written from the status document. | `cfa09f5e2c4` |

## Checking a file against the research branch

The copied files can be compared byte for byte with the commit they came from,
in a clone that has fetched `research`:

```bash
C=07123926e88273271344977a3fdc26d1780cde14
git show $C:evidence/integrate-20261111/TAS_FinalB.lean   | cmp - docs/r1/TAS_FinalB.lean
git show $C:evidence/integrate-20261111/TAS_G0_AUDIT.json | cmp - docs/r1/TAS_G0_AUDIT.json
git show $C:evidence/ledger30-20261111/NNN_LEDGER.json.xz | cmp - docs/r1/NNN_LEDGER.json.xz
xz -dc docs/r1/NNN_LEDGER.json.xz | shasum -a 256   # 347ee3c30027821df0264b2152ac36c003cd822d03e03b149d2ddc2da73ffe82

S=docs/research/100bit-spend-path-20261013/design/SOUNDNESS-CLAIM-DRAFT-20261108.md
git show cfa09f5e2c4:$S | cmp - docs/r1/SOUNDNESS-STATUS.md
git diff cfa09f5e2c4 research -- $S   # what has changed on research since the copy
```

The other files are written up from the research evidence rather than copied,
and each names, in its opening lines, the research paths it was taken from; the
security contract and the trust inventory reproduce their sources with only the
headings moved down a level. Replaying the proofs themselves needs the research
branch, its pinned Lean workspace and its compiled dependency caches. The
receipt directories named in these files record, for every compile, the exact
command, exit status, wall time, peak memory, swap, source revision and printed
axioms.

The R1 source on `main` can be compared with the frozen revision directly:
`crates/`, `programs/r1-cost-probe` and `Cargo.lock` are byte-identical to
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, and `programs/aspis-pool` to
`b936275465600469312d1f058cdc91ea2a11f3dc`, so
`git diff 4bb3b3f51e16 -- crates programs/r1-cost-probe Cargo.lock` shows only
the folder README.
