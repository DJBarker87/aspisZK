# Current privacy status

Date: 2026-09-12

Base source revision:
`9e432896a4e1515efebe940b71fd9b4f9f009189`.

Status: **SOURCE_RUST_TEST_PASS; SAME-PUBLIC VALID-WITNESS ATTACK REPRODUCED; LEAN_LEAF_COMPILED; full-view adaptive ZK fails for the current q22 path**.

## Decisive findings

1. The actual crate-private circle encoder confirms the supplied nonzero
   annihilator for semantic column 3 on q22 schedule `0..21`, conditional on
   the separately reconstructed repaired inventory and balancing rule. The
   harness skips row 1014 and represents each inactive direction as
   `E(e_r)-E(e_1023)`; it does not invoke the full repaired prover or establish
   the Python matrix's rank 56.
2. A same-public valid-witness pair is now constructed: both input slots use
   the same note commitment and only `selected_second` differs. Public
   statements and snapshots are byte-identical; both transfers pass. Their
   semantic traces differ at rows 913 and 1017. The q22 fibres 4 and 6 expose
   row 913, with functional values `1959911333` and `303025598` in M31 and
   nonzero delta `490597912`; actual mask application preserves the delta.
3. The row-1014 displacement is not exposed by every q22 schedule. Five
   tested consecutive schedules had column-3 rank 56 and exposed it; 32
   deterministic pseudorandom distinct schedules had full raw rank 88 and hid
   it. This is a bounded falsification result, not a bad-schedule probability
   bound.
4. The repository has a real pre-publication GoodSpend rank gate, but it is
   the q18 Spend path. The selected q22 generated performance path constructs,
   verifies, serializes and writes the proof without calling
   `state_only_hiding_rank`, `check_state_only_complete_hiding_rank`, or a
   `probe_*rank` entry point.
5. The frozen demonstration uses
   `StateOnlyAttemptSecrets::deterministic_spend_fixture` and an in-memory
   nonce store. It is functionality evidence, not the entropy-backed real
   privacy experiment.
6. Seven of the ten generated-input transformations are reconstructible from
   pinned repository content and the committed overlays. Three required
   preimages have no matching SHA-256 in any local Git revision:
   `programs/aspis-verifier/src/v7_pair_forest_dispatch.rs`,
   `programs/aspis-verifier/src/lib.rs`, and the LiteSVM harness
   `main.rs`. P0 therefore remains open.

## Gate ledger

| Gate | Status | Evidence or blocker |
|---|---|---|
| P0 source/profile reconstruction | PARTIAL | Pins and 18 objects verified; 7/10 transformations reconstructible; 3 preimages unavailable locally |
| P1 literal raw diagnostic | CLOSED narrowly | Fixed-schedule column-3 annihilator passed against actual encoder; repaired inventory/balancing separately reconstructed |
| P2 deficient-schedule meaning | CLOSED–FAIL | Same-public pair and q4/q6 separator; fixed-pair event probability is `11/1636171776` under uniform distinct q22 sampling |
| P3 honest entropy/session game | SPECIFIED, adapter open | See `HONEST_PROVER_EXPERIMENT.md` |
| P4 public view | INVENTORIED, source projection open | See `PUBLIC_VIEW.md` |
| P5 joint/conditional maps | OPEN | Only generic algebra and raw C1 fixed-schedule certificate checked |
| P6 efficient simulator | CLOSED–FAIL | Same-public separator rules out a statement-only simulator at the intended privacy level |
| P7 seed/salt/FS hybrids | OPEN | Cache coherence helper only; no programming/conflict bound |
| P8 prover/publication refinement | REPAIR REQUIRED | q22 path lacks a pre-publication legal-image gate; entropy adapter remains open |
| P9 global composition | BLOCKED BY ATTACK | Current q22 bytes cannot receive a full-view adaptive-ZK claim |
| P10 proof validation | PARTIAL | Generic leaves and FS draft compile; no independent kernel replay |
| P11 semantic independent review | REVIEWED for this milestone | Read-only adversarial review retained in `SEMANTIC_REVIEW.md`; not an independent human audit |

## Proved, tested, and not proved

Machine-checked generic facts include finite coin transports, affine
translation/separation, balanced-mask parametrization, simultaneous
corrections, inactive-sum preservation, retry bookkeeping, visibility
projection, conditional-kernel composition, gate-preserving release,
deterministic hybrid triangle accounting, the exact `2ε` same-public
separator obstruction, and literal profile arithmetic.
Their source instances are not constructed.

The Rust tests prove the stated annihilator identity against the actual
encoder under the reconstructed layout rule and its mask-seed-invariant value
on the tested valid transfers. Python and Rust tests do not prove source-level
privacy, adaptive scheduling, a same-public valid-witness obstruction, or any
global advantage bound.

No deployment, transaction, wallet/key operation, force push, merge, full
project replay, Aeneas run, SBF build, or generated-certificate aggregation was
performed.
