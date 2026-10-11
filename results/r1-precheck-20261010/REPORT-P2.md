# P2 — UNPROVED R1 COST PROBE

**S1, S2 and D have completed measurements; none fits 1,400,000 CU per
transaction.** S1 was measured and reported first, followed by S2 and D.
The artifact-retention requirement has one disclosed failure: the initial S1
native executable was overwritten before archival. This report does not
close the P2 acceptance or complete-evidence gates.

Base `600eb013878a0169cdab8f222e879cd395e3a1e2`; branch
`codex/r1-precheck-p2-20261010`. The Libra clarification and fold-count note
were read from `docs/research/v8-r0-rust-20261009/PLAN.md` at
`d461532985ac7e3a94dc84c5dc27346216629c1a`. These are isolated cost
experiments in `aspis-r1-cost-probe` and `aspis-r1-cost-probe-program`, with
their own prover. They are not reference implementations.

## Measurements and fit decision

The completed figures below are **DIAGNOSTIC**, using an elevated 200M-CU
runtime limit. Each transaction was also attempted five times per fixture
at 1,400,000 CU: **all 60 attempts failed at the CU meter**. No transaction
pair completed at that limit. No variant has positive headroom to 1,300,000.

- **S1: one fold, final256, k=14.** Transfer transaction totals are
  **3,331,310 / 3,439,672 CU**; withdrawal **3,327,648 / 3,438,697 CU**.
  Pair totals: 6,770,982 / 6,766,345 CU. Query folds plus rho accumulation
  cost about 2.714M across the pair; relation rounds and pairing about 1.849M.
- **S2: two folds, final64, k=10.** Transfer totals are
  **2,441,407 / 2,411,848 CU**; withdrawal **2,435,353 / 2,414,242 CU**.
  Pair totals: 4,853,255 / 4,849,595 CU. Relation rounds and pairing fall to
  about 1.059M; query folds plus rho accumulation still cost about 1.806M.
- **D: two folds, final64, k=22.** Transfer totals are
  **3,541,584 / 5,714,586 CU**; withdrawal **3,542,936 / 5,716,002 CU**.
  Pair totals: 9,256,170 / 9,258,938 CU. Materialized point tensors dominate
  the 5.466–5.468M relation phase. Even moving every query to tx1 leaves
  tx2 substantially larger.

Each cell below is **transfer / withdrawal**. Phase markers include logging
cost; their sum, including entry/exit, equals the program subtotal. A further
356 CU per transaction appears in the harness's transaction total; headroom
uses that total. Earlier progress reports quoted the program subtotal.

| Phase / metric | S1 tx1 (k=14) | S1 tx2 (k=14) | S2 tx1 (k=10) | S2 tx2 (k=10) | D tx1 (k=22) | D tx2 (k=22) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Parse | 91,767 / 91,715 | 40,308 / 40,308 | 56,875 / 56,823 | 36,136 / 36,136 | 56,875 / 56,823 | 36,136 / 36,136 |
| Semantic | 903,170 / 899,866 | 0 / 0 | 903,170 / 899,866 | 0 / 0 | 903,098 / 899,224 | 0 / 0 |
| Prepare | 443,997 / 444,193 | 0 / 0 | 489,141 / 489,020 | 0 / 0 | 489,227 / 488,945 | 0 / 0 |
| Checkpoint read | 0 / 0 | 126,936 / 126,960 | 0 / 0 | 114,865 / 114,779 | 0 / 0 | 114,853 / 114,763 |
| Merkle | 96,931 / 96,905 | 55,419 / 55,405 | 100,280 / 100,222 | 120,355 / 120,480 | 220,626 / 220,602 | 0 / 0 |
| Query folds and rho accumulation | 1,727,850 / 1,727,374 | 986,076 / 985,605 | 822,065 / 819,546 | 983,707 / 986,011 | 1,801,882 / 1,807,466 | 0 / 0 |
| Relation rounds and pairing | 0 / 0 | 1,848,829 / 1,848,282 | 0 / 0 | 1,059,165 / 1,059,243 | 0 / 0 | 5,466,043 / 5,467,555 |
| Final rho evaluation | 0 / 0 | 375,587 / 375,620 | 0 / 0 | 94,175 / 94,148 | 0 / 0 | 94,109 / 94,103 |
| Checkpoint write | 65,930 / 65,930 | 4,855 / 4,855 | 68,211 / 68,211 | 1,783 / 1,783 | 68,211 / 68,211 | 1,783 / 1,783 |
| Entry/exit and other overhead | 1,309 / 1,309 | 1,306 / 1,306 | 1,309 / 1,309 | 1,306 / 1,306 | 1,309 / 1,309 | 1,306 / 1,306 |
| Program subtotal CU | 3,330,954 / 3,327,292 | 3,439,316 / 3,438,341 | 2,441,051 / 2,434,997 | 2,411,492 / 2,413,886 | 3,541,228 / 3,542,580 | 5,714,230 / 5,715,646 |
| Other transaction overhead CU | 356 / 356 | 356 / 356 | 356 / 356 | 356 / 356 | 356 / 356 | 356 / 356 |
| Total transaction CU | 3,331,310 / 3,327,648 | 3,439,672 / 3,438,697 | 2,441,407 / 2,435,353 | 2,411,848 / 2,414,242 | 3,541,584 / 3,542,936 | 5,714,586 / 5,716,002 |
| Headroom to 1,300,000 | -2,031,310 / -2,027,648 | -2,139,672 / -2,138,697 | -1,141,407 / -1,135,353 | -1,111,848 / -1,114,242 | -2,241,584 / -2,242,936 | -4,414,586 / -4,416,002 |
| Proof bytes | 95,735 / 95,735 | 95,735 / 95,735 | 122,231 / 122,231 | 122,231 / 122,231 | 122,231 / 122,231 | 122,231 / 122,231 |
| Checkpoint bytes | 8,968 / 8,968 | 8,968 / 8,968 | 2,824 / 2,824 | 2,824 / 2,824 | 2,824 / 2,824 | 2,824 / 2,824 |
| Peak heap bytes | 31,656 / 31,656 | 15,680 / 15,680 | 19,472 / 19,472 | 6,616 / 6,616 | 19,928 / 19,928 | 55,312 / 55,312 |
| Acceptance at 1,400,000 | 0/5 / 0/5 | 0/5 / 0/5 | 0/5 / 0/5 | 0/5 / 0/5 | 0/5 / 0/5 | 0/5 / 0/5 |

## Gates and comparison method

The sampler and K-arithmetic changes passed the byte-preserving gate against
retained, unmodified S4 semantic data on both fixtures **before** the D14
Libra content was added. The gate covers semantic challenges, states,
polynomials, claims, terminal and masked terminal; 4,610 sampler blocks and
9,220 circle-map checks match. All 397 high-component mutations per fixture
reject. That gate and S4 measurements were not rerun. See
[semantic-equality.json](semantic-equality.json) and the historical
[semantic-gate report](REPORT-SEMANTIC-GATE.md).

The subsequent D14 content is a protocol change, checked against the dense
native evaluator rather than S4 byte identity. Both fixtures pass native
acceptance in each variant. The dense evaluator uses literal 1,024-entry
functional rows, E-valued semantic evaluation, direct natural-basis
calculations and a dense 4-by-4 solve for the second fold. It shares field,
wire and transcript primitives with the probe. Every emitted challenge,
weight and check value agrees bitwise: **20,465 values per fixture for S1**,
**10,699 for S2 and D**. This includes raw and dual-folded weights, relation
boundaries, query products, rho accumulator entries and final equalities.
The S2 semantic prefix is also checked byte-for-byte against S1. Checkpoint
serialization round-trips byte-for-byte.

The mutation corpus rejects **1,422 cases per fixture for S1**, and **898
per fixture for S2 and D**. Cases cover header, semantic message tags and
values, opening claims, relation polynomials, folded root, final coefficients,
opened values, authentication paths, truncation, checkpoint bytes and public
binding. These are finite self-consistency and rejection checks.

Each variant has one final call-graph stack audit. All find **zero reachable
stack diagnostics**. The conservative analysis includes all linked functions
as potential indirect-call targets: 211 functions for S1/S2 and 212 for D.
The compiler's 34 diagnostic functions (57 lines) are absent from each linked
artifact. Stripped and unstripped executable-text hashes agree. The largest
heap high-water mark among all completed diagnostics is **56,148 bytes**
(D's k=0 tx2), below 262,144. The table shows the chosen-split peaks.

| Variant | Native and dense evidence | Mutation evidence | Stack audit | Split selection |
| --- | --- | --- | --- | --- |
| S1 | [native gate](S1/native-gate.json) | [transfer](S1/transfer-mutations.json), [withdrawal](S1/withdrawal-mutations.json) | [audit](S1/stack-audit/stack-audit.json) | [k=14](S1/balance-selection.json) |
| S2 | [native gate](S2/native-gate.json) | [transfer](S2/transfer-mutations.json), [withdrawal](S2/withdrawal-mutations.json) | [audit](S2/stack-audit/stack-audit.json) | [k=10](S2/balance-selection.json) |
| D | [native gate](D/native-gate.json) | [transfer](D/transfer-mutations.json), [withdrawal](D/withdrawal-mutations.json) | [audit](D/stack-audit/stack-audit.json) | [k=22](D/balance-selection.json) |

One transfer k=0 diagnostic per variant supplied query-prefix costs for
choosing k; the next measurement changed that instruction input. Tx1 at k=0
already exceeds 1.4M in every variant. Chosen-split diagnostics then completed
on both fixtures. When a capped tx1 failed, the harness attempted tx2 in
isolation using the matching completed diagnostic checkpoint; every JSON
labels that origin. Those attempts are not successful transaction pairs.
The requested five capped repetitions were run once as a set. No completed
measurement set was rerun unchanged.

## Implemented probe shape

S1/S2 use base-4 digit-position reversal and identity within each digit. D
uses the current D13 transport. Initial commitments have 29 lanes, domain
2^20, fibres of four, and two eight-way trees. Leaves pack M31 lanes in four
bytes and K lanes in 16 bytes. The batched coefficient vector uses gamma in
E. No chord quotient is computed.

The seven functionals are the inactive 0/1 row (kappa^0), three point rows
(kappa^1–3), the extra row (kappa^4), and two natural-basis OOD rows
(kappa^5–6). The extra row is coefficient-indexed: alpha8^j for j<28,
alpha9^(j−28) for 28≤j<56, then zero. All 29 extra claims are in semantic
row 25 before z0. Lane 28 holds the two degree-27 K polynomials there; the
terminal and mask-sum claims include the lead-specified contributions.
OOD challenges remain circle points over K.

Fold challenges and relation polynomials are E-valued. Each 4-to-1 fold uses
one degree-6 relation polynomial with a boundary check. Structured point and
OOD weights use digit products and dual folding; D materializes point tensors.
The S2/D folded oracle has 2^18 E values, grouped into 2^16 four-value leaves
and padded with fixed zero leaves to an eight-way depth-six tree. Queries
follow the same initial fibres through both oracles. Final-message
coefficients number 256 for S1 or 64 for S2/D. Rho is sampled after the
query set; the verifier accumulates its natural-basis weight vector and
performs one final coefficient pairing.

The implemented S1 opening schedule is gamma, kappa, alpha0, query set,
rho (rows 27–31); S2/D add alpha1 (rows 27–32). The explicit S1 list matches
the lead note, but 27 semantic rows plus those five opening rows gives
**32 labelled rows**, whereas the note says 33. No extra dummy round was
invented. This arithmetic discrepancy remains documented; no formal round
accounting result is asserted.

Tx1 parses, verifies semantics, prepares, checks the first k queries, and
writes a checkpoint. Tx2 parses the wire, reads and checks that checkpoint,
checks remaining queries, then relation and final equalities. The checkpoint
contains transcript state, proof/public bindings, prepared challenges,
roots, query indices, counters, rho power and scalar accumulator, and the
final-basis weight vector. It is a program-owned local account and includes
a checksum for mutation detection. This experiment establishes no general
checkpoint integrity property. Proof/public and checkpoint accounts are
preloaded by the local harness; loading the proof and rent costs are outside
these verifier CU measurements. The 95,735/122,231-byte proof is account data,
not a transaction instruction payload.

## Resources, source identity and retention exception

All 31 build/gate scopes ran on `nuc` at MemoryHigh 4 GiB, MemoryMax 6 GiB,
MemorySwapMax 0, with aggregate reservation checks. Peak sampled aggregate
RSS was **1,242,001,408 bytes**, peak cgroup memory **982,884,352 bytes**,
and observed swap zero. No cap was raised. Proof generation and dense gates
used optimized release binaries. Two compile-only failures were corrected
before measurements: isolated-module imports, then native-only trace storage
and the custom allocator feature. The first SBF attempt did not link; its
logs are retained. Final audits cover the linked artifacts actually measured.

Source revisions in execution JSON identify the then-current commit
`19d8f2023`; exact dirty input hashes are in each job's source manifest.
[source-replay.json](source-replay.json) retains eight successful build-stage
source versions as content-addressed UTF-8 JSON blobs where they differ from
the final tree. It verifies every manifest hash without rebuilding. S2's
inactive-weight product hoist preceded its first build; D's dense-point
product hoist preceded its first build. Earlier measurements retain their
own source identities. The final tree contains both changes.

[build-host-artifacts.json](build-host-artifacts.json) records SHA-256 and
size for 43 retained executable/proof/checkpoint/text/disassembly artifacts
(32,207,090 bytes). Files remain under
`/home/dombarker/project-offloads/aspis-r1-p2-20261010/results/r1-precheck-20261010/`.
Generated task keys are retained securely on that host and excluded from
copied evidence. Committed evidence contains JSON, Markdown and logs only.

**Retention exception:** S1's initial native-gate executable was overwritten
in the private Cargo cache by the S2 build before it was archived or hashed.
Its native result JSON, trace hash, rejection corpus, capped build/run logs,
exact source manifest and reconstructable source are retained. Its proof and
public files and both SBF artifacts are also retained. The missing native
executable's hash and size cannot be supplied. This violates the requested
artifact-retention rule; no unchanged run was made to conceal or repair it.
S2 and D native executables are archived and hashed.

[evidence-audit.json](evidence-audit.json) checks resource caps, all 18
completed diagnostic transactions, all 60 failed capped attempts, phase
reconciliation, native gates, artifact hash cross-links, historical source
hashes and the change-path whitelist. It explicitly records the retention
requirement as **unmet**. No Lean, reference prover, reference verifier,
`r0/onchain.rs`, or retained fixture path was modified. P2 ends with negative
CU results and the disclosed evidence exception; no configuration meets the
lead's fit rule.
