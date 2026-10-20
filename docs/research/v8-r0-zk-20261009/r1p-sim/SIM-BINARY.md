# Binary-format simulator (PROOF-SIZE-OBLIGATIONS item 5)

Branch `codex/cx-sim-bin-20261020`; base `f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5`.
The change adds new privacy Lean modules and ports only simulator-side Rust
and its measurement gate. No existing Lean module or verifier source is edited.

## Lean statements and definition audit

The literal `simE` is a payload function, not an oracle programmer:
`lean/R0Z/RefPayload.lean:154` returns metadata and the shifted reference
coset at the public challenges and tape. Its definition has no tree arity.
The programming operation is `R1Z.GamesR1.progOracle`
(`lean/R1Z/GamesR1.lean:119`), which looks up `verLog`; `verLog` is the
transcript log followed by `W.comLog` (`GamesR1.lean:114`). The binary
`fsR1P` retains this ideal game (`GamesR1PBin.lean:206`). Thus the correction
belongs at the simulator's log and binary real-game bridge, not in the
algebraic payload definition.

Actual binary definitions used:

- `GamesR1PBin.lean:45`/`:50`: 2^18 fibres and seventeen non-root binary
  levels; roots are separate coordinates.
- `LayoutR1PBin.lean:119`/`:128`: node bytes `0x12` plus two 32-byte
  children, and the commitment address grammar.
- `LayoutR1P3Bin.lean:255`: opened reads are the three roots, opened leaves
  and nodes with `u / 2^(level+1)` equal to the node index. Salts, seed
  derivations and expander positions are excluded from verifier reads.
- `EventsR1PBin.lean:45`/`:54`/`:105`/`:111`: `batchReadSet`, `ROpen`,
  `ansC`, and `RComLog`. `ROpen` requires two individually deduplicated
  batches and coverage of the aggregate opened fibres. `RComLog` relates
  `W.comLog` to mapped prover positions **on honest views**.
- `LayoutCountR1PBin.lean:15`/`:20`: `n1 = 115 + McR1 + 2`, worst case
  2,457,717 when E₁ = 90,112 and E₂ = 8,192.

New proofs, all sources under `lean/R1Z/`:

1. `SimulatorSupportBin.lean:12`, `equalLaws_output`: finite equal-law
   samplers have the same possible outputs (symbolic finite sums only).
2. `SimulatorLogR1PBin.lean:22`, `simE_honest_preimage`: from the actual
   `hvzk_R1S` (`SimulatorR1.lean:30`), on P_R1 ∧ VR1 and a matching public
   witness, every simulated view has an honest-view preimage tape. This is
   an existence proof; no witness or choice enters the simulator algorithm.
3. `SimulatorLogR1PBin.lean:36`, `simE_comLog_batches`: transports RComLog
   through that view equality, then applies RCommitBytes. The actual
   simulated comLog is two mapped lists of **binary `gram` addresses** with
   `ansC` answers. Each list is Nodup, its toFinset equals `batchReadSet`,
   its length equals that set's cardinality, and the two fibre sets unite
   to `Pr.openFib`. No extra simulator-wire hypothesis is introduced.
4. `SimulatorLogR1PBin.lean:75`, `simE_progOracle`: the actual lookup at
   transcript ++ simulated comLog, with fallback on absent addresses.
5. `PrivacySimulatorBin.lean:20`, `privacy_R1_eff_binary`: applies the
   original `SimulatorR1.privacy_R1_eff` (`SimulatorR1.lean:74`) directly
   using `FinalR1PBin.realModel_R1P`, the Bin ideal model, the spend sampler
   law, and D76 arithmetic. For N=8 and q≤2^64 the error is
   **2^-109 + 2^-137**. The inherited named premises remain explicit.

Final env-J attempts are **6100, 6105, 6106**, respectively support, binary
log, dependent privacy root: exit 0; 2.72/1.65/1.91 seconds; peak RSS
3,362,004/3,379,508/3,838,352 KiB; zero swaps. All five theorem reports use
only `[propext, Classical.choice, Quot.sound]`. `attempts.jsonl` retains full
output, SHA-256, dependency fingerprint, revision, timing and failed attempts.
6101 lacked the VR1 namespace; 6104 needed explicit expander dimensions on
`gram`. Both were corrected in source before new attempts; no false
mathematical target or counterexample was found. 6102/6103 are superseded
successful intermediate statements. 6106 recompiles the root after 6105's
strengthened log statement. `manifest.json` is the final focused packet.

Modules/objects present at the branch base were reused, not overwritten.
Only this job's new modules were replaced during iteration, with source/object snapshots under
`aspis-joint-20261019/snapshots/codex-cx-sim-bin-20261020/` on the host.
Each attempt used the existing run-joint launcher, env J, -M7000, 7 GiB cap,
MemoryHigh=5G, MemorySwapMax=0. No unchanged package regression was rerun.

## Rust algorithm and measurements

`crates/aspis-r1-cost-probe/src/sim.rs:356` stores a sparse binary tree;
`:368` programs leaf hashes and eighteen levels of distinct parents over
the union of opened fibres. The final parent receives the root coin.
Unopened siblings receive coin digests without programming their preimages.
`ProgrammedTree::multiproof` uses the adopted `multiproof::generate`
(`src/multiproof.rs:180`) for each sorted/deduplicated transaction batch.
Shared ancestors and folded leaves use one consistent tree/table.

`sim.rs:459` serializes the adopted codec: magic, compact semantic records
and y1, remaining logical records, 22 value/salt openings, then six padded
node slots. It checks the 57,607-byte length. `compact.rs:86` and `:109`
reject nonzero high halves when compacting; `:127` and `:148` reconstruct
zero halves in the verifier. The 32-byte C1/C2/folded root digests stay at
the same rows (`sim.rs:162`, `walk`). The transcript recording pass uses
logical records and exactly 115 answers (`sim.rs:485`), preserving the
adopted transcript. Slot padding and sibling bytes add no oracle reads.
`sim.rs:505` invokes the unchanged strict tx1+tx2 and dense verifiers.

Host `evidence.json` records exact commands, source and artifact hashes/sizes,
raw time receipts and per-run values. Optimized Rust jobs used separate
systemd scopes (MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64),
-j4 and `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. Populated reservations
were 28.375 GiB before the main 8 GiB scope and 32.375 GiB before the focused
8 GiB overlap-test scope, below the 55 GiB aggregate limit.

| Check | Result | Wall | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|
| Release build | exit 0 | 30.87 s | 563,748 | 0 |
| Original simulator tests, unignored | 3 pass, 0 ignored | 85.03 s incl. compile | 641,720 | 0 |
| New overlap/adjacent/shared-node test | 1 pass | 5.36 s incl. compile | 336,484 | 0 |
| Four OS-seed simulator runs | 4/4 pass | 149.16 s | 326,428 | 0 |

Every gate run accepted on its first attempt, produced 57,607 bytes, passed
strict tx1+tx2 **and dense under the programmed oracle**, and failed strict
stage 1 **and dense under the real hash**. Programmed/read counts were
1,042/1,039/1,042/1,060 (each exactly 115 transcript + commitment addresses).
Simulation took 36.409–38.424 s: P_R1 35.019–37.029 s, semantic summation
1.356–1.597 s, opening 4.38–5.27 ms, programming/serialization 29.1–37.8 ms;
without P_R1, 1.390–1.641 s. Verification took 6.12–8.00 ms.

The restored teeth tests reject consistently programmed simulations without
S₀ or the round-9 shift. The new focused test exercises repeated leaves
across batches, adjacent siblings and shared ancestors, and checks that the
union of actual reads is exactly the programmed domain. It was added after
the three original tests completed, so only that new test was then run.

## Scope and remaining premises

This is a conditional privacy result and an executable simulator test, not
an extracted Rust-to-Lean refinement proof. The inherited ROM, causal prover,
commitment grammar, mask decoder/equal fibres, expander/exhaustion and R-wire
premises remain named hypotheses. D77's transcript/node length separation is
not discharged by this job. The seeded hash coin expander and prover mask
expander stand in for independent uniform coins and a uniform tape; their law
correspondence remains the existing R-commit obligation. P_chk ⇒ P_R1 retains
the checker's source-refinement premises. No wallet keys are created or removed.

## LOG-ready entry

PROOF-SIZE-OBLIGATIONS item 5: the explicit Rust simulator now emits the
adopted 57,607-byte compact binary multiproof format and programs the
transcript, opened leaves and binary path union. Unignored acceptance and
ablation tests plus a shared-batch test pass. Four optimized host OS-seed
runs pass strict tx1+tx2 and dense under the programmed oracle and fail
under the real hash; 36.4–38.4 s total, ≈1.4–1.6 s excluding P_R1; every
programmed address read. New privacy modules prove that simulated comLog
uses exactly two deduplicated binary batchReadSets on the HVZK domain,
without an extra simulator-wire premise, and re-prove the bounded binary
privacy_R1_eff root. Final J attempts 6100/6105/6106, exit 0, standard axioms,
≤3.67 GiB, zero swaps. Sources and receipts: `r1p-sim/manifest.json`,
`attempts.jsonl`, `evidence.json`; correspondence updated in
`r1p-retry/CORRESPONDENCE-G-SIM.txt`. No existing Lean or verifier module
changed. Source refinement and D77's transcript-length discharge remain
open as before.
