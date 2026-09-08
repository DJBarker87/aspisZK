# V7 all-reachable CU bound: PDA and residual-tail closure

Date: 2026-09-08

Branch: `research/v7-all-reachable-cu-bound-testnet-20260902`

Starting HEAD: `e5640f79133f8afbeb7eb08a940abc6462274295`

Measured-binary source HEAD: `acc4055b6c55ff6a568cf0d3d916365eccb4ebf1`

Evidence implementation commit: `e5e4edf133044fd8c70c1924c75333c9e6492bfd`

Rollover harness commits: `4499ec7dad9a296d1d63783fb2a6849df1652f29`,
`b7e2e0f52384c00183349677d40552adf23cd71f`,
`3568b7e2479bd824db42af799c299d7deaf5245a`,
`c21c0b8058f54b2eeab3bbf737c3a65224f6c12c`, and
`d3a0829508e2beba792ab48623636f595f9b8606`.

Genuine rollover-withdrawal evidence commit:
`b22c2b709d618f45e0d9b3a7cd733693fde390b5`.

Ending HEAD: the immediate report-hygiene successor to the evidence commit;
recorded exactly by `git rev-parse HEAD` in the handoff.

Classification: **B — RELEASE-MARGIN GREEN**

## Result

For the default-off cutoff-20 publication policy and default-off authenticated
terminal-PDA certificate, the conservative all-reachable successful terminal
ceiling is **1,311,862 CU**. This leaves **88,138 CU** below Solana's
1,400,000-CU hard transaction limit and **38,138 CU** below the preferred
1,350,000-CU release gate. It remains 11,862 CU above the aspirational
1,300,000-CU project gate. No production promotion, public deployment, or
identity selection was performed. `mainnetReady` remains false.

This is a source-bounded current-profile result, not a claim that one sampled
transaction exercised every maximum simultaneously. Four genuine current-binary
transactions for all four terminal shapes provide combined anchors.
Independently finalized probe
transactions cover the complete successful QM31 retry topology, counter 0 to
20, all q16/order work, and the complete accepted frontier grammar from 14 to
203. The former 120,706-CU rollover envelope is retained for provenance but is
no longer used in the current ceilings.

## Source state and `main`

`origin/main` was fetched at `9dae54750b5e1e70e8b1a0d933ebc3ebe33e918e`.
The merge base is `bff78d6eab006dfc75c704abde824fa7c57637b1`.
No runtime, Pool-program, verifier-program, harness, or CU-bound path in this
CU-closure scope changed on main after that merge base. The newer main-only
work is the independent K1/fold formal series, including
`V7MerkleTypedTruncateCongruence`; it is not a dependency of the persisted-PDA
or terminal-CU argument.

Two relevant changes were already ancestors of this branch:

- `44c55bcb` preserves archived harness source provenance;
- `7dcaee5b` promotes the deposit-only invariant path, which does not alter the
  terminal transfer/withdrawal CU graph.

No cherry-pick was required. Importing the independent K1 work would have been
out of scope and would have invalidated the measured source/binary pairing. The
machine-readable audit is in
`results/v7-all-reachable-cu-bound-pda-closure-20260908/main-integration-audit.json`.

## PDA inventory and deterministic closure

The original successful terminal paths contained:

| Shape | `find_program_address` before | `find_program_address` after | Fixed single attempts after |
| --- | ---: | ---: | ---: |
| transfer, same page | 18 | 0 | 11 |
| transfer, rollover | 19 | 0 | 12 |
| withdrawal, same page | 20 | 0 | 15 |
| withdrawal, rollover | 21 | 0 | 16 |

The full source/function/program/seeds table is
`source-inventory/terminal-pda-inventory.json`. It distinguishes Pool master,
checkpoint, selected lane, current/next history page, nullifier marker,
Registry V2, Registry ProgramData, Registry entry, verifier ProgramData, vault
authority, and vault token account. It also records duplicate derivations and
why the nullifier bump cannot be accepted as an unauthenticated user input.

The APD8 certificate is initialized after proof sealing and before the terminal
transaction. Initialization performs the twelve canonical descending searches,
checks a one-attempt replay for every exact seed/program-id identity, and writes
a 704-byte verifier-owned immutable image. Terminal execution:

- reauthenticates the certificate owner, proof/attempt binding, Registry,
  release/profile/program identities, exact flags and all address bytes;
- uses `create_program_address` with the authenticated canonical bumps;
- compares the generated addresses with all supplied accounts;
- keeps account ownership, PDA identity, capacity, history-page, lane,
  inactive-frontier, vault, marker and ProgramData checks;
- rejects corrupt bytes, wrong bumps, wrong identities and noncanonical schema;
- never writes the certificate.

The maximum terminal PDA cost is therefore exactly 16 fixed attempts × 1,500 =
**24,000 CU**. There is no successful variable bump-search tail. This adds one
readonly account and 33 transaction bytes. Existing Pool account layouts,
proof bytes, statement bytes, relation, TxV1 encoding and CPI order are unchanged.
The terminal-PDA certificate and cutoff publication policy remain default-off.

## Formal invariant

`AspisFormal/Pool/V7TerminalPdaCertificateInvariant.lean` proves:

1. initialization stores the canonical address/bump for the exact identity;
2. the enumerated writer relation only initializes or preserves the bytes;
3. every reachable persisted entry remains canonical by induction;
4. single-attempt replay returns the canonical searched address;
5. old search acceptance and certified single-attempt acceptance are equivalent
   on reachable authenticated state;
6. a corrupted bump that does not recreate the recorded address fails closed;
7. the pointwise result covers all twelve APD8 classes.

The source boundary is explicit: this is a representation-independent Lean
induction whose identities/writer surface are pinned to literal Rust by
`scripts/v7_terminal_pda_inventory.py`. It is not claimed to be a new
Charon/Aeneas extraction. No new axiom, `sorry`, `admit`, or unsafe shortcut was
introduced.

Focused replay:

```text
cd AspisFormal
lake env lean AspisFormal/Pool/V7TerminalPdaCertificateInvariant.lean
```

Exit 0; 1.23 s wall; 432,308,224-byte peak RSS; zero swap. All nine
`#print axioms` lines report `does not depend on any axioms`. The successful
stdout and resource record are under `formal/`. An initial evidence wrapper
used zsh's readonly variable name `status`; that wrapper failure is retained,
then the identical Lean target was replayed successfully with `lean_exit`.

## Current binaries and genuine combined anchors

Agave was pinned to 4.2.2 (`c9c6f328`, platform tools v1.54). Disposable
validators activated SIMD-0385/TxV1 at genesis under feature ID
`txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL`. Only audit identities and
task-owned funds were used.

| Binary | SHA-256 |
| --- | --- |
| current Pool | `cb5f90452ddd0772c5401f42ed0e28b7a38b7bb93ea0ac465cfab37fe7afd1a2` |
| current selected-sort verifier | `8894c98c21583bdbd08f891367ece6fcb7570cbc53058250f4f87b5372260c66` |
| CU-tail probe | `f71713a8c50bdb62111012856332a364f7800a68e604e6d6de0ed343f812ec04` |
| cutoff-20 host prover | `5f51fb6b28c852b68f3d9d9b0710b92b4252db2253c3744504672282c847d3a7` |

All four genuine terminal transactions had one Pool terminal instruction plus
the canonical real-HPKE ciphertext carrier, were simulated with signature
checking, submitted byte-identically, and finalized:

| Case | Counter/frontier | Bytes | verifier CPI CU | landed CU | Slot |
| --- | ---: | ---: | ---: | ---: | ---: |
| transfer, same page | 8 / 196 | 1,411 | 1,000,153 | **1,029,881** | 710 |
| withdrawal, same page | 1 / 201 | 1,576 | 976,371 | **1,014,941** | 803 |
| transfer, rollover | 0 / 200 | 1,444 | 970,996 | **1,066,928** | 897 |
| withdrawal, rollover | 9 / 203 | 1,609 | 1,010,821 | **1,115,624** | 1,035 |

Transfer signature:
`56VSaHfPycbg4neR4SiQCyUs6yb6EDLzrLB62guzQb4ipJHSL38KPdrXkEaTKXYyc9VjvD8UWGanH4riCCyLEoTq`.
Wire SHA-256:
`4be3c7fd9e427cd5b55578e9529b7d0648cbc1b3d24f8e719209355787f49e28`.
Its genuine 30,460-byte proof hash is
`35398d2cd7313ec094e4b4eff59e7d58506d9e1e11e7a3f2fab3c3e51a31b9d0`.

Withdrawal signature:
`2k29sHbCZgNCNERuHEe1DCNoQuZWuWCvRF2cmaHzVoHkwsH4Gbd6pz5ra3LCaCkDBZFvXqg8r7qBnjoFn7GumVoi`.
Wire SHA-256:
`b6fe8f98e9b2f57f0e36c4d2089a7ddb2ba5441c1d0f4d93e22c379b25afbac9`.
Its genuine 30,720-byte proof hash is
`6f896f82b2e8cffc7f45ae28325ac550df989b8fc6904709ac0bbc5402a8ee76`.
Custody changed vault 1,000→750 and bound destination 0→250 for amount 250.

Rollover transfer signature:
`5aUJ4Q4PCPScBQpZyGCFd7vBs7Hwp1KcAxRiLdphxXotUdoHLBxSf9b6zVP59bwFR8b7FUHWapKBoXdGMJvm9rpW`.
Wire SHA-256:
`8a8fed16cc16d1854c626944dc4e06f113ff295133e50dd03300f884c896f46e`.
Its genuine proof hash is
`fa309f9e6d5dc0ec5ada3331dc93b228fd028da95b418f494a5380374ce894fe`.

Rollover withdrawal signature:
`238yAUJGP3BecrVW56FNZv5Qq2WeUSZ9oBZi5X4h6BEX3GDKo8WRohjsuFbAML8pecW38HQh3b6rEfbXk9KHQGok`.
Wire SHA-256:
`f685e733fbc146ee5249e2e361db764161f415e3b8a9261d229b69e3b07acbb7`.
Its genuine proof hash is
`37edc3b5bb6a006486f2ff6bba2b945423e6f5dc5764b5f6d4f051c79c526b32`.
Custody changed vault 255,000→254,750 and the bound destination 0→250.

Simulation CU equalled landed CU in all four cases. All proof accounts were
finalized closed and drained/refunded. Exact before/after JSON hashes, replay
and fresh-nullifier replay rejection, finalized RPC records and closure
receipts are under the two `current-*-selected-sort/` and two
`current-*-rollover-direct/` evidence directories. No private key or
wallet-state binary is included.

Each rollover fixture independently finalized 254 sequential deposits, then
derived its live witness from lane 0 at pair index 254/root sequence 255. The
terminal append crossed the page boundary using the canonical precreated,
zeroed, 8,256-byte, Pool-owned next history page. The prefill transactions were
dependency ordered; every simulated/landed CU pair and signed wire matched.
The highest precursor-deposit CU was 553,034. This is a genuine live rollover,
not a synthetic Pool envelope.

Two earlier genuine proofs could not reach the terminal step because the first
finalized proof-upload transaction record was unavailable before the 35-write
upload set was audited. This was consistent with pruning: Agave test-validator
defaults to retaining 10,000 shreds. The harness now requires at least
1,000,000 retained shreds, passes that value to `--limit-ledger-size`, and
records it in `ledger-configuration.json`. The successful transfer replay used
that setting. The failed attempts and the diagnosis are retained in
`negative-evidence/direct-rollover-attempts.json`; neither is presented as
terminal execution.

Proof wall time was 287.745 s and 465.668 s for the same-page transfer and
withdrawal. The rollover proofs took 191.002 s and 287.690 s. That variance is
the existing proof-of-work search. Cutoff selection was enabled, required the
minimum q16 draw path, and selected counters ≤20.

## Residual tails

The isolated probe is a mutually exclusive, local-validator-only verifier
entrypoint. It executes the real SHA syscall before controlled successful
sampler outputs. Every signed wire was simulated and submitted byte-identically
and finalized.

| Dimension | Minimum CU | Maximum CU | Full delta |
| --- | ---: | ---: | ---: |
| exact accepted QM31 topology | 22,748 | 93,935 | **71,187** |
| q16/order: best vs worst, 21 candidates plus accepted opening | 23,722 | 33,892 | **10,170** |
| cutoff counter 0 vs 20 | 4,910 | 85,852 | **80,942** |
| accepted Merkle frontier 14 vs 203 | 14,779 | 97,414 | **82,635** |
| diagnostic frontier 199 vs 203 | 95,687 | 97,414 | 1,727 |

The first probe bundle measured only frontier 199→203. That was insufficient
for an all-grammar statement and is retained as negative evidence. The revised
probe pins the mathematical minimum: 16 contiguous leaves form a complete
depth-four subtree, hence 14 authentication nodes. Its first run then exposed
a blockhash expiry on the ninth finalized case; the runner now refreshes at
cases 4 and 8. The successful nine-case run took 2:01.58, peaked at 703,220 KiB,
and used zero swap.

### QM31

Current source contains 30 direct QM31 samples, four nonzero wrappers and two
secure-circle wrappers. Accepted execution reaches 36..48 successful QM31
calls and 36..192 squeeze blocks. A QM31 sample uses 1..4 blocks; each outer
wrapper uses 1..3 accepted QM31 samples. The secure-circle subfield precheck
prevents a variable failed rational-map inversion. The complete accepted
topology—not only SHA syscall charges—was measured above. Challenge
distribution was not changed.

### Query ordering and q16

Cutoff 20 admits 1..21 candidates. Every candidate must obtain 16 distinct
queries in its first two squeeze blocks. The source-visible insertion loop has
15..120 comparisons per candidate, or 315..2,520 over 21 candidates, plus
15..120 comparisons for the accepted opening. The selected audit build routes
all three production 208-bit opening consumers through that helper; default
builds retain the library sort. Focused equivalence tests compare its output
with the standard sort. Proof/query semantics are unchanged.

## Conservative arithmetic

The common tail envelope is:

```text
  cutoff-20 full counter range                    80,942
+ accepted frontier grammar 14..203               82,635
+ complete successful QM31 retry topology         71,187
+ worst query order, 21 candidates + opening      10,170
= common tail envelope                            244,934 CU
```

The historical rollover envelope was:

```text
  complete production-shaped Pool rollover path  119,206
+ one extra current fixed PDA validation            1,500
= superseded rollover envelope                    120,706 CU
```

The 119,206-CU reference includes the Pool prefix, authenticated verifier
transport, marker handling, rollover-page checks/writes and suffix. It is not
misreported as a real-proof combined measurement. Adding the entire value to a
genuine current combined same-page transaction double-counts all common Pool
work and verifier transport. Current rollover source additionally requires a
precreated exact-size zeroed Pool-owned next page and one fixed PDA validation;
it performs no terminal System account creation. As corroboration, the
independent 256-deposit run measured only a 49,078-CU same-page→rollover delta
(594,776→643,854), far below the 120,706-CU envelope.

It is retained as a conservative cross-check only. Direct current-binary
rollover anchors now replace it in the release arithmetic.

For each shape, the generator adds the complete independently measured range
for every residual dimension unless the genuine anchor already exercises that
dimension's exact maximum. The rollover withdrawal proof has exactly 203
frontier nodes, so its remaining frontier term is zero. All other nonmaximum
anchors conservatively receive the complete 14→203 range; the arithmetic does
not infer a per-node coefficient.

Final shape ceilings:

| Shape | Arithmetic ceiling |
| --- | ---: |
| transfer, same page | 1,029,881 + 244,934 = **1,274,815** |
| transfer, rollover | 1,066,928 + 244,934 = **1,311,862** |
| withdrawal, same page | 1,014,941 + 244,934 = **1,259,875** |
| withdrawal, rollover | 1,115,624 + 162,299 = **1,277,923** |

The arithmetic intentionally adds each full residual range even though each
anchor is already inside the counter/order/retry ranges. The maximum measured
serialized wire is 1,609 bytes, below both 3,500 and 4,096 bytes.

No accepted data-dependent runtime branch remains outside this arithmetic for
the cutoff-20 profile. The unchanged verifier language still accepts counters
through 63 and is **not** covered by the cutoff-20 CU guarantee.

## Focused validation and resources

Commands are reproduced exactly in `replay-commands.txt`.

- verifier tail probe: 4/4 focused tests passed; 3.64 s; 352,944,128-byte peak
  RSS; zero swap;
- selected query sorter equivalence: passed; 11.90 s; 676,528,128-byte peak
  RSS; zero swap;
- Lean PDA invariant: exit 0; 1.23 s; 432,308,224-byte peak RSS; zero swap;
- current Pool SBF: 1:17.15; 545,952 KiB peak RSS; zero swap;
- current verifier SBF: 24.85 s; 523,764 KiB peak RSS; zero swap;
- revised probe SBF: 2.04 s cached; 230,780 KiB peak RSS; zero swap;
- revised host probe builder: 18.75 s; 898,508 KiB peak RSS; zero swap;
- successful nine-case runtime: 2:01.58; 703,220 KiB peak RSS; zero swap;
- genuine withdrawal lifecycle: 10:18 wall; 2.3 GiB systemd peak; zero swap;
- genuine transfer lifecycle: 7:17.80 wall; 1.5 GiB systemd peak; zero swap;
- genuine rollover withdrawal lifecycle: 9:15.50 wall; 2.3 GiB systemd
  peak; zero swap;
- genuine rollover transfer lifecycle: 7:41.21 wall; 2.2 GiB systemd peak;
  zero swap;
- focused rollover materializer/genesis-preparer release check: 0.46 s;
  102,055,936-byte peak RSS; zero swap; focused `rustfmt --check` passed.

All NUC builds/runs used explicit systemd `MemoryHigh`/`MemoryMax` limits no
larger than 8/10 GiB and `MemorySwapMax=0`. Nothing approached the 12-GiB stop
threshold. Broad regressions and frozen CU profiling were not run.

## Changes, migration, and release implications

Runtime changes are limited to default-off audit features:

- verifier-owned APD8 initialization and immutable certificate replay;
- Pool/verifier fixed-bump terminal plumbing;
- source-visible selected-opening sorting for bounded CU analysis;
- the mutually exclusive disposable CU-tail probe;
- harness blockhash refresh required by nine sequential finalized probes.

The APD8 approach moves canonical searches to preparation; it does not reduce
total network work, but it removes their variable tail from the one terminal
transaction. Promotion would require a release decision and one additional
preterminal account/init transaction. Existing Pool state requires no migration.
Production identities and release artifacts were deliberately not selected.

The earlier public-Devnet evidence is unchanged. No new public-Devnet verifier
was deployed because the task expressly required local/source closure first.
This report is neither
public-Devnet lifecycle evidence nor mainnet readiness evidence.

## Remaining work

The all-reachable cutoff-20 bound and preferred release margin are closed, but
production release engineering is not:

1. Review migration and operational handling of the additional verifier-owned
   APD8 certificate account and its preparation instruction.
2. Decide whether to promote the two default-off audit features. That requires
   production identities and release governance outside this task.
3. Only after that decision, build the exact release binaries and execute a new
   disposable public-cluster lifecycle. The current evidence must not be
   relabelled as public-cluster or mainnet evidence.

The branch is safe to cherry-pick as research/default-off audit infrastructure.
It is **not** safe to enable in production solely from this report: identities
are audit-only, the APD8 migration/release decision is outstanding, and no
production release was signed.
