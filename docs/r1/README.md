# R1 proof package

This folder is the part of the R1 soundness evidence that fits on `main`: the contract the work is held to, the current status, the two top-level theorems with their audit, the table of the 599 verified statements, the trust inventory, the devnet run, the build recipe and the open gates. Everything here was taken from the `research` branch at commit `07123926e88273271344977a3fdc26d1780cde14` (9 November 2026), and each file names the research path it came from. The full evidence, about 45 GB of Lean sources, compiled objects, receipts and logs, stays on that branch; nothing in this folder replaces it, and the release target, 100-bit classical per-attempt soundness for the actual spend path, is not yet established.

| File | What it is | Taken from (research `07123926e88`) |
| --- | --- | --- |
| [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md) | The status document: the theorem in prose and Lean, every binder and retained hypothesis, the exact numeric bound and its valid range, the trust it relies on, what is not claimed, and the gates still open | `docs/research/100bit-spend-path-20261013/design/SOUNDNESS-CLAIM-DRAFT-20261108.md` |
| [`TOP-THEOREM.md`](TOP-THEOREM.md) | The two compiled top-level theorems, printed by Lean, with a plain reading of each binder and the axiom and closure audit | `evidence/integrate-20261111/TAS_G0_AUDIT.json` |
| [`TAS_FinalB.lean`](TAS_FinalB.lean) | The Lean source of the two theorems (copy) | `evidence/integrate-20261111/TAS_FinalB.lean` |
| [`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json) | The full audit record of the final assembly (copy) | `evidence/integrate-20261111/TAS_G0_AUDIT.json` |
| [`LEDGER-599.md`](LEDGER-599.md) | One line for each of the 599 verified statements: row, Rust function, domain and root theorems | `evidence/ledger30-20261111/NNN_LEDGER.json.xz` |
| [`NNN_LEDGER.json.xz`](NNN_LEDGER.json.xz) | The complete ledger (copy, 1.1 MB compressed) | `evidence/ledger30-20261111/NNN_LEDGER.json.xz` |
| [`SECURITY-CONTRACT.md`](SECURITY-CONTRACT.md) | The binding security contract with all approved amendments, followed by the ARX amendment | `docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md` and `design/SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md` |
| [`TRUST-INVENTORY.md`](TRUST-INVENTORY.md) | Every named trust row: the current table, then the approved appendix with its later additions | status document section 4, and `design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md` |
| [`DEVNET-RUN.md`](DEVNET-RUN.md) | The devnet deployment of 29 October 2026: ELF hash, program ids, signatures, what settled and what was rejected | `evidence/devnet-rehearse-20261029/` |
| [`BUILD.md`](BUILD.md) | How the release ELF is built, the overflow-check setting, and the reproduction receipt | `evidence/finish-pair2-20261027/`, `evidence/native-elfpins-20261028/` |
| [`OPEN-GATES.md`](OPEN-GATES.md) | Each open release gate in a paragraph, with what would close it | status document section 6 |

## How to check it

The quickest check is to compare the copies with the research branch. From a clone that has fetched `research`:

```bash
C=07123926e88273271344977a3fdc26d1780cde14
git show $C:evidence/integrate-20261111/TAS_FinalB.lean   | cmp - docs/r1/TAS_FinalB.lean
git show $C:evidence/integrate-20261111/TAS_G0_AUDIT.json | cmp - docs/r1/TAS_G0_AUDIT.json
git show $C:evidence/ledger30-20261111/NNN_LEDGER.json.xz | cmp - docs/r1/NNN_LEDGER.json.xz
xz -dc docs/r1/NNN_LEDGER.json.xz | shasum -a 256   # 347ee3c30027821df0264b2152ac36c003cd822d03e03b149d2ddc2da73ffe82
```

Replaying the proofs themselves needs the research branch, its pinned Lean workspace and the compiled dependency caches. The attempt numbers quoted in these files (for example NNH_L945 for the combined import and NNH_L942 to NNH_L944 for the axiom walks) name receipt directories under `evidence/integrate-20261111/` on that branch, each recording the exact command, exit status, wall time, peak memory, swap, source revision and printed axioms. The project's rule is to compile the smallest target first and to run the full closure only once, under capped memory, after the focused targets pass; a coherent cold replay of the final closure is itself one of the open gates.

The R1 source on this branch can be compared with the frozen revision directly: `crates/`, `programs/r1-cost-probe` and `Cargo.lock` are byte-identical to `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, and `programs/aspis-pool` to `b936275465600469312d1f058cdc91ea2a11f3dc`, so `git diff 4bb3b3f51e16 -- crates programs/r1-cost-probe Cargo.lock` shows only the folder README.
