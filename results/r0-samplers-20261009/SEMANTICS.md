# R-F — P1 semantic rows 0–24

Source commit: `5e509cae0`. Base: `805f9c102`. Branch: `codex/r0-semantics-rf-20261009`.
R-B prerequisite: `f87a2d55d`, cherry-picked as `0b11caacf` (the sole conflict retained both `pub mod r0` and `pub mod r0_transcript`). R-F uses its pure `qm31_sample` / `circle_sample` functions; it does **not** use R-B's provisional `0x80+i` row helper.

The default-off `r0` feature provides a separate semantic prover/parser/verifier. All seven existing source files remain byte-for-byte prefixes of their modified files: the R0 modules are appended and no legacy function is edited. `semantic-scope-audit.json` checks this against the requested base. No file under `crates/aspis-core/src/r0/` or any Lean tree was changed.

## Wire and entrypoints

- `state_only_candidate_prefix::r0::build_pair_forest` builds H1 with the existing PF helper; `build_with_helper` supports an already prepared/masked PF helper. The helper is invoked exactly once, after C1 and lambda/chi. Its errors abort; chi is never retried. The builder always evaluates the PF terminal, not a caller-selected semantic oracle.
- `state_only_verify::r0::verify_semantics` checks the semantic sumcheck/terminal and the two circle rows. **Its result is not complete proof acceptance.** R-D still supplies encoded-word commitments, opening verification and authentication.
- The commitment backend receives C1 `[0..25,28]` before lambda/chi and C2 `[26,27]` afterwards. `Commitments::c1` takes 26 F columns plus D in K; `Commitments::c2` takes exactly H1,G. This is the R-F commitment timing/lane boundary, not a replacement R552 tree implementation. The deterministic integration-test backend hashes message bytes and is explicitly not a Merkle authentication test.
- Semantic wire is C1 root (32 bytes), then 27 exact P1 records through `beforeZ1`: **12,903 bytes**. Every record is `tag:u8 || length:u32_le || payload`, including the empty records. Semantic messages use E's full 32-byte canonical encoding; semantic challenges are K values embedded in E. No upper E limb is silently discarded or required to be zero by the verifier.
- C1-time context binding follows SPEC §9's explicit IV formula: `SHA256(domain || 00 || public_length || public_bytes || C1_root)`. Thus statement/root are in that single initial hash, and **row 0 still absorbs `00 || 00000000`**. There is no extra profile/statement/root row. `public_bytes` follows `R0P.Public` order and canonical F encoding; the Rust public index is already a u64.
- For R-D's `SemanticBoundary::from_verified_parts`, use `state_before_z0`, the two roots, `challenges.with_alphas(&alpha)`, and all 87 claims from the successful semantic result. R-D starts by replaying row 25. Do not pass the diagnostic transcript's later row-27 state. The separately retained `before_z1` is the exact row-26 message; there is deliberately no equality restriction against row 27's repeated Y0.

## Per-row change table

Paths below are repository-relative; C = `crates/aspis-core/src/`, H = `crates/aspis-prover/src/`, S = `crates/aspis-statement/src/`. Every scalar row goes through C/state_only_prefix.rs:1737–1758: one P1 absorb, one block, one advance, and R-B's rejection-free modulo sampler. No scalar row has a zero filter.

| Model row / label / challenge | Rust change (including removed legacy operations) | File:lines |
|---|---|---|
| C1 context | Bind exact public bytes and C1 root in the §9 IV; C1 lanes are 0–25,D. Replace legacy PROFILE, BASIS, statement-digest, hiding-context/mask-nonce and indexed C1-root absorbs. | S/pool_v1/pair_forest_semantic_terminal.rs:2002–2041; C/state_only_prefix.rs:1722–1729; H/state_only_candidate_prefix.rs:791–801 |
| 0 / a0 / λ | Empty tag-00 record followed by `qm31_sample`; D is already committed. Replace legacy limb-retrying scalar draw. | C/state_only_prefix.rs:1644–1653,1857; H/state_only_candidate_prefix.rs:800–809 |
| 1 / a1 / χ | Add required empty absorb before one block. Preserve helper pole abort; no retry. | C/state_only_prefix.rs:1858; H/state_only_candidate_prefix.rs:810–816,934–941 |
| 2 / a2 / θ | One tag-01 C2 root record, H1,G only. Remove separate legacy root/constraint-registry/helper-zero-sum absorbs; D is not adaptive C2. | C/state_only_prefix.rs:1647,1859; H/state_only_candidate_prefix.rs:816–817 |
| 3 / a3 / zc[0] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 4 / a4 / zc[1] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 5 / a5 / zc[2] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 6 / a6 / zc[3] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 7 / a7 / zc[4] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 8 / a8 / zc[5] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 9 / a9 / zc[6] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 10 / aa / zc[7] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 11 / ab / zc[8] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 12 / ac / zc[9] | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1646,1860–1863 |
| 13 / ad / μ | Empty tag-00 absorb before one modulo block; replaces unframed legacy squeeze. | C/state_only_prefix.rs:1864; H/state_only_candidate_prefix.rs:822 |
| 14 / ae / η | Tag 03, exactly one E mask sum. Remove degree/round metadata bytes and `challenge_nonzero_qm31`; η=0 succeeds after one block. | C/state_only_prefix.rs:1648,1865; H/state_only_candidate_prefix.rs:833–861 |
| 15 / af / α[0] | Tag 02, 28 canonical E coefficients; boundary then Horner update. Remove legacy round-index payload byte (index is the row label) and limb-retry draw. | C/state_only_sumcheck.rs:589–621; H/state_only_hiding.rs:1444–1485 |
| 16 / b0 / α[1] | Same row driver, polynomial 1; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 17 / b1 / α[2] | Same row driver, polynomial 2; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 18 / b2 / α[3] | Same row driver, polynomial 3; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 19 / b3 / α[4] | Same row driver, polynomial 4; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 20 / b4 / α[5] | Same row driver, polynomial 5; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 21 / b5 / α[6] | Same row driver, polynomial 6; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 22 / b6 / α[7] | Same row driver, polynomial 7; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 23 / b7 / α[8] | Same row driver, polynomial 8; one record and one block. | C/state_only_sumcheck.rs:609–617; H/state_only_hiding.rs:1452–1479 |
| 24 / b8 / α[9] | Polynomial 9; compare final running E claim to `maskValueClaims(y0)+η·PF_terminal`. Save the state before circles. | C/state_only_sumcheck.rs:609–621; S/state_only_verify.rs:1176–1187 |
| 25 / b9 / z0 | Tag 04, point-major 3×29=87 E claims, D at each row's lane 28. Remove derived-point absorb, legacy 84-value absorb, separate D absorb, batch PoW guard/nonce, and premature gamma/point-scale squeezes. Use the one-block reference-circle map. | C/state_only_prefix.rs:1650,1762–1772,1813–1823; H/state_only_candidate_prefix.rs:749–759,876–882 |
| 26 / ba / z1 | Tag 05, 29 E natural-circle values. Remove legacy batched OOD-value record and intervening OOD-mix squeeze. No retry; equality rejects. Retain this message separately from future row-27 values. | H/state_only_candidate_prefix.rs:883–903; S/state_only_verify.rs:1188–1207 |

The remaining legacy fold/final nonce absorbs, work checks, four-fold schedules and query-selection draws are not called by the R0 entrypoint. Opening row 27 and beyond remain R-D's responsibility. No R0 grinding mode or nonce exists here.

## Terminal and parser details (V01–V15)

V01/V11/V12: the returned semantic result must still pass R-D opening/authentication; no full-proof soundness claim is made. V02/V03/V04/V06/V07: `Prefix::parse` fixes all 27 tags, lengths, positions, canonical E limbs and suffix exhaustion before replay. V05: public F typing is checked here; committed F/K word typing/authentication remains the commitment/opening interface. V08: claim storage/serialization/point evaluation is 3×29 with no special detached D record. V09: R-B's reference map plus an explicit `z0 != z1` guard. V10: beforeZ1 is retained but not equated with a later record. V13/V14: literal boundaries and final terminal equality in E. V15: the existing pair-forest amount and transition guards remain reject-only guards.

The PF expression at S/pool_v1/pair_forest_semantic_terminal.rs:1303–1309 is unchanged and contains `eq(zc,alpha)*composition + mu*H1 + mu^2*(1-active)*H1`. The R0 adapter at :2044 keeps point strides at 29 when selecting the 28 terminal-active lanes. D's three claims are preserved for the opening batch but its mask/semantic terminal factor is zero, as in the model.

To support canonical E claims without weakening the parser, the adapter at :2073 extends the existing K polynomial evaluator by deterministic interpolation in `t`, substituting every claim `c0+t*c1` and evaluating at `t=v`. At fixed K challenges/coordinates its degree is at most 25: two successive fifth-power Poseidon steps give 25; Copy gives at most five; the other families at most three. Twenty-six base-field nodes therefore suffice. This is a source arithmetic construction, **not a new soundness premise or a machine-checked refinement theorem**. Honest embedded-K claims take the existing single-evaluation fast path. The mask evaluator at C/state_only_hiding.rs:1190 applies its K-linear formula separately to both E coordinates. Tests check the inactive-H1 term with H1=v and mu=3, obtaining 12v.

## Validation and evidence

- `semantic-core-final.log`: 4 passing tests. Each of rows 0–26 has tag/length/short/long/order/repeat teeth; every E limb (including the last element) rejects p; every truncation rejects; each sumcheck boundary rejects an added v component. Zero eta takes one block; the fixed circle fallbacks are distinct. The independent fixture checks every challenge, state and exact hash input count (one IV plus three hash reads per row).
- `semantic-boundary.log/json`: 3 optimized Linux tests pass: honest PF prover/verifier, public byte serialization, and a separate sparse fixed trace matching the independent Python polynomials, all 87 claims and all 29 natural-circle values. The honest test mutates statement/root/semantic and D claims and beforeZ1. D-only mutations change z0/state and remain an opening-layer obligation, as intended.
- `semantic-circle-equality-verified.log/json`: the remaining focused test forces the same non-CM31 parameter at both circle rows; rejection is `EqualCirclePoints`, with no resampling.
- `semantic-legacy-transcript.log`: 34 pass (9 R-B sampler tests, 18 legacy transcript tests including all pinned KATs, 7 V6/V7 transcript tests). `semantic-legacy-profiles.log`: all 8 state-only tests pass, including profiles 18/19/20/21/22/23/rate256 and their separate schedules. Pins were not updated.
- `semantic-no-std.log/json`: release checks for core and statement with `r0`, no default features, pass. `semantic-default-off.log` checks the prover with no default features, also passes.
- `generate_semantic_kat.py --check` reproduces the fully independent sparse-trace fixtures byte-for-byte. `check_honest_semantics.py` independently checks the deterministic honest trace's two test-backend roots/partition, all row hashes, mask total, all ten boundaries, 87 MLE claims and 29 beforeZ1 natural-code evaluations. It reads the fixed exported trace/proof, not Rust-computed challenges. It does not duplicate the PF residual implementation or claim to test Merkle authentication.

The final optimized PF/boundary gate spent 33.68 seconds compiling and 2.73 seconds in tests (36.58 seconds wall including the runner), sampled peak aggregate RSS 1,028,516 KiB, cgroup memory peak 832,851,968 bytes, exit 0, swap peak 0. Every Linux gate used MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0. Combined reservations were checked against the 62 GiB host; the later 15 GiB reservation sum includes R-D and Z4a. Local focused checks had a 6 GiB aggregate-RSS stop and two build jobs. No dense/debug arithmetic or Lean job ran locally.

The first Linux attempt stopped before compilation because the copied workspace manifests/lockfile were inconsistent. Its exit-101 record is retained in `semantic-honest.json/log`; synchronizing the pinned workspace inputs fixed it. Subsequent reruns correspond to added evidence exports, the explicit row-25 handoff, and the added equality test, not unchanged full regressions. Each runner records its source hashes/revision, target, status, time and memory; final hashes are in `semantic-source-manifest.json`. `#print axioms` is not applicable (Rust-only; no Lean edits/replays).

Honest proof SHA-256: `fed9bcbb8cdc4183d01dc23a7b2baef4c5324a037a243ab2f62d7a984f0338f8`.
Sparse independent proof SHA-256: `b319090aae9dcd709bf779953ae93b2c05cd89c7ed376347b15ac4ee13e203b6`.
