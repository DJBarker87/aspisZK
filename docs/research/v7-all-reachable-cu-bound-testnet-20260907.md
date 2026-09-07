# V7 all-reachable CU audit and public TxV1 activation — 2026-09-07

## Result

**CURRENT TAG-73 PROFILE CU BASELINE IS MISSING; THE ALL-REACHABLE COMPLETION
BOUND FAILS CLOSED. PUBLIC TESTNET AND DEVNET TXV1 FEATURES ARE ACTIVE;
MAINNET IS NOT ACTIVE.**

Counter 20 remains a useful measured publication policy, but it is not a
universal proof that every published terminal transaction completes below
1,300,000 CU or Solana's 1,400,000-CU transaction limit. The policy bounds the
q16 candidate counter and removes the q16 duplicate-draw tail. It does not
bound the independent QM31 rejection samplers, query-ordering work, or PDA
bump searches on the Pool/verifier terminal path.

This audit changed no verifier, Pool, TxV1, cryptographic relation, proof
format, SBF binary, tree depth, or CPI ordering. It did not build SBF, generate
a proof, deploy a program, sign a public transaction, or spend funds.

Branch: `research/v7-all-reachable-cu-bound-testnet-20260902`.

Original CU-audit base revision:
`4c91f97ac6576201f90d41c2a575e54c026e3796`.

Current merged production-source revision:
`b053663d6c4fc7e991ef08ca568f68b81d25311c`.

The final evidence commit is reported in the handoff because a commit cannot
contain its own hash.

## Profile-revision-2 supersession

Main subsequently merged `b053663d`, which causally binds the complete raw
sampler output for Tag-73 gamma and alpha-zero. The compact transcript profile
revision byte changed from 1 to 2. Proof bytes did not grow, but the accepted
transcript language and production verifier source changed. Consequently,
every CU/byte figure below remains authentic **historical profile-revision-1
evidence** and is not a current-binary measurement.

Revision 2 adds exactly two SHA-256 calls. Each hashes four slices of lengths
32, 2, 2 and 384 bytes. Under the inspected Agave schedule, each syscall costs
313 CU and the exact fixed syscall component is 626 CU. This is deliberately
not added to an old transaction measurement: the new recorded-block copying
and control flow also change SBF instruction cost. A fresh production SBF
build and genuine revision-2 proof are required.

The optimized host verifier rejects the saved genuine revision-1 proof with
`Transcript(TerminalRejected)` (exit 1). This establishes fail-closed profile
separation; it is not an SBF CU measurement.

The designated memory-intensive build host, `nuc.tail0cfe7a.ts.net`, was
offline when checked. Repository policy therefore prevents the required SBF
rebuild and fresh honest proof run from being substituted with an uncapped
local build. Current-profile simulated CU, landed CU and transaction bytes are
recorded as `null`, not inferred.

The live terminal builder now inventories PDA-search cost before signing for
the authenticated immutable Registry V2 path. It records every unique PDA,
bump, attempts per invocation, runtime multiplicity and the exact 1,500-CU per
attempt syscall component. The call counts are 18 for same-page transfer, 19
for rollover transfer, 20 for same-page withdrawal and 21 for rollover
withdrawal. It also derives the nullifier marker by identity, fixing a
harness-only reporting error where a hard-coded account index named the next
history page as the marker during rollover.

The host proof inspector now counts actual 33-byte transcript squeeze hashes,
reports squeeze blocks, and requires exactly two `[32, 2, 2, 384]` causal-bind
hash calls before accepting a revision-2 proof. No current proof exists yet to
populate those diagnostics.

## Public feature activation

At finalized commitment on 2026-09-07, the direct feature-account probe found:

| Cluster | Genesis hash | Feature state | Activation slot | Activation epoch | RPC core |
| --- | --- | --- | ---: | ---: | --- |
| Testnet | `4uhcVJyU9pJkvQyS88uRDiswHXSCkY3zQawwpjk2NsNY` | active | 437,276,256 | **1025** | 4.3.0-beta.3 |
| Devnet | `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG` | active | 492,480,000 | **1140** | 4.3.0-beta.3 |
| Mainnet-beta | `5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d` | absent/inactive | — | — | 4.2.2 |

The feature is
`txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL`. Both present accounts are
owned by `Feature111111111111111111111111111111111111` and encode bincode
`Some(activation_slot)`. Testnet's account bytes are
`01604e101a00000000`; Devnet's are `0100a65a1d00000000`. The latter is a
change from the earlier dated devnet-inactive evidence: Devnet activated at
slot 492,480,000 on 2026-09-03. Historical snapshots were not rewritten.

The Solana Foundation's canonical [larger transaction status
page](https://solana.com/upgrades/larger-transaction-sizes) now also displays
Testnet **Active**, Devnet **Active**, and Mainnet **Not activated**. The
feature-account state is the fail-closed runtime authority used here. The
canonical [TxV1 reference](https://github.com/solana-foundation/solana-dev-skill/blob/main/skills/solana-dev/references/transactions-v1.md)
identifies version 1 as the 4,096-byte transaction format and documents direct
feature-account inspection.

This is activation evidence only. No Aspis program is deployed or exercised
on either public cluster, and it is not finalized public lifecycle evidence.
`mainnetReady` remains `false`.

## Historical profile-revision-1 measurements retained

No frozen CU path was rerun. The evidence distinguishes three previously
captured contexts:

| Context | Counter/frontier | Bytes | Total CU | Qualification |
| --- | ---: | ---: | ---: | --- |
| Frozen combined terminal baseline | 0 / historical | 997 | 1,201,757 | one terminal transaction, eight lanes |
| Then-current rollover withdrawal | 0 / 202 | 1,043 | 1,218,972 | genuine strict-work LiteSVM sample; profile revision 1 |
| Live disposable cutoff-20 withdrawal | 9 / 202 | 1,543 | 1,196,956 | genuine finalized Agave 4.2.0 local sample |

The then-current sample used Pool SHA-256
`9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d`
and verifier SHA-256
`97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d`.
The 1,218,972-CU measurement is the historical source anchor below, not an
upper bound and not applicable to profile revision 2.

The prior two-point calibration remains:

```text
ceil(1,218,972
  + (frontier_nodes - 202) * 451.290322580643
  + counter * 3,983.010752688172)
```

It predicts 1,299,084 CU at counter 20/frontier 203, leaving 916 CU below the
project's 1.30M gate and 100,916 CU below the runtime limit. Its maximum fit
error on the two controlled comparisons was one CU. It is still a calibrated
envelope, not an all-reachable theorem.

## Source-derived bounded control flow

### q16 schedule

The default-off cutoff policy publishes counters 0 through 20 inclusive and
requires the first 16 q16 words of every evaluated candidate to be distinct.
That fixes q16 sampling to two squeeze blocks per candidate and at most 42
blocks over 21 candidates. The unchanged verifier language still accepts
counters through 63 and permits up to 64 draws, or eight blocks, per candidate
before rejection.

`binary_frontier_nodes` insertion-sorts every 16-query candidate. Distinct
query order gives 15 through 120 insertion comparisons per candidate, hence
315 through 2,520 comparisons over 21 candidates. The accepted opening also
sorts 16 entries. Counter 20 does not constrain this ordering. No standalone
SBF-CU coefficient for these comparisons is manufactured from the two-point
calibration.

### Field challenges

The exact accepted Tag-73 flow contains 30 direct QM31 challenges, four
nonzero-QM31 wrappers, and two secure-circle wrappers. The outer wrappers may
each consume one through three successful QM31 samples. A successful QM31
sample consumes one through four transcript squeeze blocks because each of
four limbs allows eight canonicality attempts.

Therefore an accepted proof reaches 36 through 48 successful QM31 calls and
36 through 192 squeeze blocks. One squeeze block performs two 33-byte SHA-256
syscalls. Under the inspected Agave 4.2.1 schedule, each such SHA syscall costs
101 CU, so the maximum successful retry path adds 31,512 syscall CU over the
minimum path. Counter 20 does not constrain it.

### PDA searches

The production-shaped fresh-marker rollover withdrawal performs 21
`find_program_address` invocations:

| Source area | Invocations |
| --- | ---: |
| Pool master/checkpoint/lane decode and selected-lane request | 4 |
| Current and rollover history-page checks | 2 |
| Nullifier plan before and after account preparation | 2 |
| Withdrawal vault authority and token account | 2 |
| Pool Registry V2 and ProgramData authentication | 4 |
| Verifier master/checkpoint/lane authentication | 3 |
| Verifier Registry V2 and ProgramData reauthentication | 4 |
| **Total** | **21** |

Agave charges 1,500 CU for every attempted program-address derivation. A
successful syscall can try bumps 255 down through 1: 1 through 255 charged
attempts, or up to 382,500 CU per invocation. Exhaustion incurs a final 256th
charge and rejects, so it is not a successful persisted transition. Across 21
successful searches, the source-level syscall ceiling alone is 8,032,500 CU,
well beyond the transaction budget; execution would abort at 1.4M before
reaching it.

Relative to an otherwise identical one-attempt derivation, one permitted
255-attempt successful search adds 381,000 CU. This is greater than the
181,028-CU headroom of the measured counter-zero rollover sample. The
resulting 1,599,972-CU figure is a comparison envelope, not a witnessed
transaction: the saved measurement does not encode every bump attempt, and no
joint SHA-256 preimage realizing all maximum branches was constructed.

Combining the calibrated counter-20/frontier-203 value with only the bounded
field-retry syscall delta gives 1,330,596 CU and 69,404 CU runtime headroom.
Forty-seven additional PDA attempts would add 70,500 CU and cross 1.4M. Again,
this is an additive reference envelope, not a fabricated landed measurement.

## Why the universal claim is blocked

The source audit establishes that the current policy leaves independently
bounded, data-dependent cost branches outside its predicate. It does not
establish a joint random-oracle preimage for the maxima, so it is not presented
as a concrete 1.4M failing proof. Conversely, absence of such a constructed
preimage is not an all-reachable upper-bound proof. A release claim quantified
over every accepted/published terminal transaction must cover these branches;
the two sampled CU coefficients cannot do so.

For profile revision 1, the exact conclusions were therefore:

- counter 20 does **not establish** completion below 1,300,000 CU;
- counter 20 does **not establish** completion below 1,400,000 CU;
- the runtime itself prevents consumption beyond 1,400,000 CU by aborting,
  which is not successful lifecycle completion;
- exact byte-identical simulation must remain mandatory; and
- the default-off cutoff feature is not safe to promote as a universal CU
  policy on this evidence.

For current profile revision 2, the conclusion is even narrower: no current
production-SBF measurement exists, so neither the 1.30M project gate nor the
1.40M runtime completion claim is established. The source-level uncontrolled
QM31, ordering and PDA branches remain relevant after remeasurement.

The smallest protocol-preserving engineering closure would remove variable
bump search from the terminal path: persist/authenticate canonical bumps and
validate them with the single-attempt `create_program_address` equivalent, or
otherwise add a release admission predicate that covers every variable path
and then remeasure the production binaries. That is a proposal only; this
branch intentionally does not change production programs or the authenticated
relation.

## Persisted-lane/deposit closure retained

The merged persisted-lane induction (`bfc3efe7`) and its finalized evidence
(`3178834e`) establish that reachable persisted lanes are genesis states or
byte-exact outputs of authenticated Pool transitions. The default-off
invariant-backed deposit path was measured across all 256 sequential deposits.
No part of that proof or code was changed or replayed here.

| Source index | Page mode | Bytes | Simulated/landed CU |
| ---: | --- | ---: | ---: |
| 0 | genesis | 651 | 640,272 |
| 1 | same page | 617 | 594,743 |
| 2 | same page | 617 | 594,683 |
| 3 | same page | 617 | 594,776 |
| 7 | same page | 617 | 594,730 |
| 15 | same page | 617 | 594,714 |
| 255 | page rollover | 684 | 643,854 |

All 256 deposits finalized in that existing disposable-cluster run; the
maximum was 643,854 CU at rollover. This does not repair the independent
terminal verifier/PDA quantifier.

## Focused validation and resources

The replay surface is intentionally small:

```text
python3 -m py_compile scripts/v7_all_reachable_cu_bound.py \
  scripts/v7_txv1_public_cluster_snapshot.py
./scripts/v7_all_reachable_cu_bound.py --pretty
./scripts/v7_txv1_public_cluster_snapshot.py --pretty
```

The source inventory ran in 0.08 seconds with 23,953,408-byte maximum RSS and
zero swaps. The three-cluster RPC snapshot ran in 8.65 seconds with
31,309,824-byte maximum RSS and zero swaps. No job approached the repository's
8-GiB local review threshold. Exact assertions, evidence, and checksums are in
`results/v7-all-reachable-cu-bound-testnet-20260907/`.

The revision-2 addendum used only focused host checks. The source audit peaked
at 23,019,520 bytes RSS; the two exact unit tests peaked at 102,514,688 and
172,032,000 bytes; and the optimized proof-inspector build peaked at
755,302,400 bytes. All recorded zero swaps. No SBF build, proof generation,
validator transaction, public signature or deployment was performed. The
revision-2 machine-readable addendum is under
`results/v7-all-reachable-cu-bound-testnet-20260907/profile-revision-2/`.
