# The proof package

This folder holds the part of the evidence for the current version of Aspis
that fits on `main`. The full evidence, some 45 GB of Lean sources, compiled
objects, receipts and logs, stays on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch, and
nothing here replaces it. The documents below are listed in the order I would
suggest reading them.

[`TOP-THEOREM.md`](TOP-THEOREM.md) is the place to start. It gives the two Lean
theorems that state the soundness of the two-transaction spend, exactly as Lean
prints them, and explains in prose what they quantify over, what they conclude,
what they assume and how the proofs were checked.

[`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md) is the full status document behind
that page. It sets out every binder and retained hypothesis, derives the
numerical bound and its valid range term by term, lists the trust the theorem
rests on and what it does not claim, and records what remains.

[`OPEN-GATES.md`](OPEN-GATES.md) describes, one paragraph per item, what still
stands between the proved theorems and the release claim of 100-bit soundness
for the version that actually runs. The main items are tying every committed
Lean translation to a fresh translation of the frozen source, a handful of
review items on the bridge from checked to wrapping arithmetic, and the pool,
whose actions the theorem's game takes as given instead of proving them.

[`SECURITY-CONTRACT.md`](SECURITY-CONTRACT.md) is the security contract the
work is held to: the game, the attacker, the failure event and the work metric,
with every approved amendment, including the one that made the attacker
arbitrary and adaptive.

[`TRUST-INVENTORY.md`](TRUST-INVENTORY.md) lists every named assumption the
proofs rest on, such as the random-oracle model of SHA-256, the behaviour of the
Solana runtime and the translation tools. It was taken before the inventory was
reconciled with the final proof closure on 10 November 2026; the reconciled
table is section 4 of the status document.

[`LEDGER-599.md`](LEDGER-599.md) has one line for each of the 599 verified
statements about the verifier's Rust, giving the function, its domain and the
theorems it rests on. It is generated from the complete ledger, of which
[`NNN_LEDGER.json.xz`](NNN_LEDGER.json.xz) is a compressed copy.

[`DEVNET-RUN.md`](DEVNET-RUN.md) records the two runs on Solana devnet, in
October and November 2026, with the deployed programs, the transactions that
settled and those that were rejected.

[`BUILD.md`](BUILD.md) explains how to build the verifier and pool programs
from the frozen source and how to check a build against the deployed programs.

[`TAS_FinalB.lean`](TAS_FinalB.lean), the Lean source that proves the two
theorems, and [`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json), the audit record of
their final assembly, are copied unchanged from the research branch.

## Where this comes from

The Lean source, the audit record and the ledger are copied unchanged from
commit `07123926e88` of the `research` branch, and can be compared byte for
byte with their source in a clone that has fetched `research`:

```bash
C=07123926e88273271344977a3fdc26d1780cde14
git show $C:evidence/integrate-20261111/TAS_FinalB.lean   | cmp - docs/r1/TAS_FinalB.lean
git show $C:evidence/integrate-20261111/TAS_G0_AUDIT.json | cmp - docs/r1/TAS_G0_AUDIT.json
git show $C:evidence/ledger30-20261111/NNN_LEDGER.json.xz | cmp - docs/r1/NNN_LEDGER.json.xz
xz -dc docs/r1/NNN_LEDGER.json.xz | shasum -a 256   # 347ee3c30027821df0264b2152ac36c003cd822d03e03b149d2ddc2da73ffe82
```

The status document and the page of open items are written up from the claim
draft on `research` at `90795727483`, and the record of the November devnet run
from `af8f9fd2f9d`.

The other documents are written up from the research evidence. The security
contract reproduces its source with only the headings moved down a level, and
the trust inventory is written up from section 4 of the status document at
`07123926e88` and the approved appendix it cites. Replaying the proofs themselves needs the research branch,
its pinned Lean workspace and its compiled dependency caches, and the receipts
there record, for every compile, the exact command, exit status, wall time,
peak memory, swap, source revision and printed axioms.

The source on `main` can be compared with the frozen revision directly.
`crates/`, `programs/r1-cost-probe` and `Cargo.lock` are byte-identical to
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, and `programs/aspis-pool` to
`b936275465600469312d1f058cdc91ea2a11f3dc`, so
`git diff 4bb3b3f51e16 -- crates programs/r1-cost-probe Cargo.lock` shows only
the folder README.
