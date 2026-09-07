# Pinned baseline and theorem map

Initial local HEAD and remote default HEAD: `4c91f97ac6576201f90d41c2a575e54c026e3796`.
Repository remote: `https://github.com/DJBarker87/aspisZK.git`. `gh pr list --state open`
returned `[]`. This research branch was created from that exact revision.
No nested AGENTS.md was found in the new worktree; root AGENTS.md applies.

Concurrent work was observed, not overwritten: main subsequently advanced to
`3ca170c6b74ca7f9897fc43813a86053bf7c47a5` (the two initially dirty Lean files),
and the existing V8 branch advanced from `00ad1d3d` to
`d9962e0d265c99172420d47566c96469c83ef7bd` with a documentation-only verdict.
The new main commit adds corrected alpha-chain proofs, not protocol parameters.
This directory stays pinned to 4c91f97a; no rebase or changes to either other branch.

Other inspected branch tips: cutoff integration `4420d842`, first-cap fix
`d42334b8`, deposit promotion `44602d36`, persisted-lane candidate `7e0f5aac`.
These have different source/benchmark scopes and are not silently merged.

## Selected source and wire

Follow `programs/aspis-verifier/src/v7_verifier.rs`, its selected canonical-fixed
reader in `crates/aspis-core/src/v7_fixed_canonical_audit.rs`, and
`v7_onefold.rs`, `v6_onefold.rs`, `v6_transcript.rs`. The compact parser alone
still describes 30,504 bytes; it is not the selected canonical-fixed body.

| Fixed section | Response QM31 values | Canonical bytes |
|---|---:|---:|
| Initial masked claim | 1 | 16 |
| Ten semantic rounds, 27 sent values each | 270 | 4,320 |
| Three point rows × 29 columns | 87 | 1,392 |
| Inactive/copy claim | 1 | 16 |
| Two scalar OOD responses | 2 | 32 |
| Four relation rounds × six sent values | 24 | 384 |
| Final disclosure | 256 | 4,096 |
| Total | 641 | 10,256 |

Two roots cost 52 bytes; three u64 work nonces cost 24. Each complete four-point
query has 104 M31 C1 values packed into 403 bytes, 12 QM31 C2 values packed into
186 bytes, and one 32-byte salt: 621 bytes. Sixteen queries cost 9,936.
Two identical-topology frontiers, each at most 203 × 26 bytes, cost 10,556.
Maximum body: **30,824**. Packing the 641 fixed fields gives 9,936 instead of
10,256, saving 320 bytes but undoing a selected CU optimization.

`state_only_hiding.rs` fixes 16 semantic C1 columns and ten mask-only C1 columns;
H/G and D form the three QM31 C2 columns (`state_only_spend_query.rs`).
The trace has 1,024 rows. Initial circle evaluation domain is 2^20; four-point
fibres have 2^18 indices. One actual arity-four FRI fold produces the final256
message. Relation rounds 1–3 are not further authenticated FRI folds.

The semantic degree is not ten. The selected pair/forest source audit bounds
it at 27; the existing exact atomic-v3 forward-difference experiment exhibits
degree 26 before the outer zerocheck and 27 after it. This run inspected that
experiment and reused the recorded result; it did not reexecute the full
semantic evaluator. The two-round Poseidon term already contributes degree 25.
Removing masks cannot justify a degree-ten counterfactual. The six-mask experiment
is closed for an unchanged degree-27 relation; it also had a six-dimensional
ambient deficit, which alone is not a same-statement privacy attack.

The account and lifecycle are separate from the body: the existing pair account
model includes a 40-byte header and 688-byte candidate afterstate. The selected
Pool CPI uses 320-byte ASQ8 and returns 792-byte ASR8. Neither is a proof body.
The final four historical transaction wires are 799/832/964/997 bytes; upload,
account creation, sealing and cleanup have separate transactions and costs.

## Transcript reconstructed from source

SHA duplex: absorb `SHA256(S || 0 || label || payload)`; squeeze output
`SHA256(S || 1)` and advance to `SHA256(S || 2)`; work check hashes
`S || 3 || nonceLE8` without advancing. Every bounded rejection advances the stream.

Order (labels are exact V7 labels): profile 1; code 11; program/release 60;
statement 2; hiding/attempt/layout 30; salted C1 root 12; lambda then chi;
adaptive C2 root 13; registry 32; zero helper sum 33; theta, ten zerocheck
coordinates, mu; initial mask claim 31; nonzero eta; ten semantic messages 48
each followed by its challenge; 87 point claims 49; semantic terminal check;
batch nonce 28; nonzero gamma; inactive claim 50; nonzero kappa; twice: secure
circle parameter, OOD value 51, mixing scalar; relation message 0 under 52;
fold nonce 20; alpha0; final256 under 53; final nonce 5; first-valid q16 scan
under 57; empty query-batch separator 58; nonzero rho; both authenticated query
trees; computed query-batch scalar 59; relation messages/challenges 1–3 under 52;
terminal dot-product check.

This has 30 ordinary QM31 scalar draws, four nonzero QM31 draws and two secure
circle parameter draws (each returning two coordinates), not 641 challenges.
Ordinary sampling allows eight 31-bit candidates per limb, at most four SHA
blocks; nonzero/circle wrappers allow three outer tries. Query candidates allow
64 draws to obtain 16 distinct indices. Up to 64 counter branches clone the
same post-final-nonce state; the verifier enforces first frontier <=203 and
continues from that branch. Sampler abort rejects. The three work nonces are
prover-selected, not enforced first successes. All selection powers survive
the no-work security diagnostic.

Typed leaves hash `0x10 || tree_tag || values || salt32`; parents hash
`0x11 || left26 || right26` (53 bytes, one padded SHA-256 block). Tags are
0x71/0xf1. Root salts bind profile, program, release, statement and attempt.
The query check is one degree-at-most-15 rho residual, not sixteen separately
accepted deterministic equalities. Production also checks canonicality.

## Historical CU evidence, not new measurements

| Shape | CU | JSON under results/ |
|---|---:|---|
| Transfer/current | 1,145,890 | v7-one-tx-sparsity-current-20260828/transfer-same-page.json |
| Transfer/new page | 1,191,463 | v7-one-tx-sparsity-current-20260828/transfer-rollover.json |
| Withdrawal/current | 1,136,135 | v7-one-tx-sparsity-current-20260828/withdrawal-same-page-counter0.json |
| Withdrawal/new page | 1,201,757 | v7-q16-source-refactor-cu-check-20260828/withdrawal-rollover-counter0.json |

JSON execution fields confirm all four numbers and no execution errors. **They
are not one common verifier binary**: the first three pin SHA-256
`fc830df85f25d4bae02138cf82a31273eda8e46b56fbfa51c00959ba26c968db`;
the fourth pins `125bba2ebe121d1bda87ba90943904ed866ba02502fc011f7156246ebb871a77`.
The earlier same-binary withdrawal rollover was 1,201,718. Pool hash for these
records is `61f80ab33bff36b38716df944d7851a473be0ed065b2d57864082fd966ec8810`.
The sparsity-lock note has still earlier numbers (e.g. 1,145,926); it is
superseded by the activation/source-refactor evidence, not silently averaged.
The separate cutoff-20 lineage records 1,218,972 for an expensive rollover
and a modeled 1,299,084 envelope; neither is the matched four-shape baseline.
No V8 complete-transaction CU has been measured here or in the prior V8 branch.

## Theorem status at the pin

| Layer | Evidence and remaining boundary |
|---|---|
| Exact fields/domains/encoder | Existing Lean exact QM31, circle/GRS conversion, initial dimension 1024 inside degree <=1024 ambient space; final degree <=255, dimension 256 |
| Decoding/list/curve | `V7ExactCorrelatedAgreement` chain proves actual initial/final encoders; strict support >38229/>9557; GS list caps 100/99. Weighted/Hensel proof already incorporated; smaller list caps alone do not replace the curve budget |
| K1.2 | Literal translated Merkle callers construct exact source obligations; SHA callback reflection remains explicit |
| K1.3 | Deterministic q16 forest and intrinsic bad-set handoff proved; actual adaptive all-actor event-measure composition remains a gate at this pin |
| K1.4/K1.5 | Coherent trace/witness and source gamma replay results exist; actual restored category/event measures and source seams remain. Operational ledger charges two distinct gamma-sized events |
| K1.6 | `V7Tag73ExactFixedK16Closure`, proof-relevant upstream interface and operational resource certificate prove the custom classical compiler conditionally on four actual upstream certificates/errors |
| Privacy | Selected concrete rank/containment evidence; programmable full-view observed-proof simulator/WUR not supplied by K1.6. New query/OOD/field views require new proofs |
| Rust/settlement | Selected Charon/Aeneas/source-shaped bridges and historical atomicity tests; full current AccountInfo-to-model and release correspondence cannot be inferred from axiom lists |

`README.md` distinguishes current V7 from archived V5. `SECURITY.md`,
`assumptions-ledger.md`, and much of `formal-verification.md` describe V5's
work-normalized endpoint; those numerical budgets do not certify V7 or V8.
Existing axiom audits report propext, Classical.choice, Quot.sound. They are
historical evidence, not a fresh formal replay in this run.
