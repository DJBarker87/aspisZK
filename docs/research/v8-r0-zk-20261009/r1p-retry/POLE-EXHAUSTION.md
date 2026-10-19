# Pole and exhaustion in the R1 real game, and the Rust retry loop

Job: LOG D73.4 items 1 and 2 (branch `codex/r1p-pole-retry-20261019`, base
74e78062c). Rust only; no Lean was compiled. Lean paths below are relative to
`docs/research/v8-r0-zk-20261009/lean/` unless stated otherwise.

## 1. What the Lean real game does

The game the privacy theorem is stated about is the phase-indexed real game
`realGameP` (R1Z/GamesR1P.lean:176–186). The earlier `realGame`
(R1Z/GamesR1.lean:204–215) has the same acceptance predicate and the same
failure branch. `privacy_R1_games'` instantiates it with `P := P_R1` and
`Vp := fun h' => VR1 h'` (R1Z/PrivacyR1P.lean:64, 71, 74).

Each of the N attempts produces an `AttemptOut` with the challenges `ch`, the
view, the verifier log and an exhaustion bit `exh` (R1Z/GamesR1.lean:173–177;
for the phase-indexed game, `attOut`, R1Z/GamesR1P.lean:152–164). The game
publishes the first attempt satisfying

    P o.ch ∧ Vp h o.ch w ∧ o.exh = false        (R1Z/GamesR1P.lean:184)

where "first" is `firstGood`, the least index satisfying the predicate
(R0Z/FsAbort.lean:55–58). An attempt that fails any of the three conjuncts
contributes nothing to the output: only `(out k).view` and `(out k).log` of
the selected `k` appear (R1Z/GamesR1P.lean:186). The model runs all N
attempts and charges every read (D52.3), which is conservative relative to
a prover that stops at the first success; the output is the same.

### (a) A LogUp pole

`VR1 h ch w := NoPole (h.build w) (ch.sem 0) (ch.sem 1)`
(R1Z/MaskImageVR1.lean:29–30), so λ = sem 0 and χ = sem 1, evaluated on the
honest trace. `NoPole` is (R0Z/HonestValidity.lean:97–99):

    ∀ b : Fin 1024, CopyActiveRow b → ∀ s : Fin 2,
      chi ≠ copyRowValues t lam b CopyLink.producer s ∧
      chi ≠ copyRowValues t lam b CopyLink.consumer s

`CopyActiveRow b` is bit `b % 16` of the fixed mask word `b / 16`
(v8-r0-sem-proof-20261008/lean/R0P/Copy.lean:240–241). `copyRowValues t lam
b endpoint slot` is the sum of the compressed tuples of the registry links
whose endpoint sits at row `b` and static slot `slot` (Copy.lean:449–452);
it does not look at the link's weight, and an unused slot has value 0.

So in Lean a pole is χ equal to any of the four slot values of any active
row, whatever that slot's weight. An attempt with a pole fails the `Vp`
conjunct: it is skipped like a P_R1 rejection, it consumes one of the N
attempts, nothing of it is published, and the next attempt runs with its own
independent secrets `r.2 k` (R1Z/GamesR1P.lean:176–186). The probability is
charged as ε_pole: `poleSet` ranges over all `activeRows × Fin 2 × Bool`
positions, at most 4,096 values (R1Z/PoleMassR1.lean:37–43, 82), giving the
term `N · 4096/(p⁴ − 1)` (R1Z/PrivacyR1P.lean:70).

### (b) Mask exhaustion within an attempt

`exh` is `(Pr.tapeOf e₁ e₂).isNone` (R1Z/GamesR1P.lean:164), where `tapeOf`
is "the mask decode of the two expander streams (none:
MaskSampleExhausted)" (R1Z/GamesR1P.lean:86–87). `RExh` ties `none` to one
of the two 16-try M31 word streams being exhausted (SeedExpander, L₁ limbs;
Profile21 D expander, L₂) (R1Z/FinalR1P.lean:49–53, statement at 51–53), with mass
`εexhP = N·16(L₁+L₂)/2^496 + M/2^255` (R1Z/FinalR1P.lean:68). An exhausted
attempt fails the third conjunct and is treated exactly like (a): skipped,
one of N consumed, nothing published, the loop continues.

### (b′) All N attempts fail

When no attempt satisfies the predicate, `firstGood` is `none` and the game
outputs `⟨W.failView, runLog (adv.prog W.failView []) H W.qmax⟩`
(R1Z/GamesR1P.lean:185). `failView` is a field of the wire structure `R1Wire`
(R1Z/GamesR1.lean:86): one fixed view, independent of the witness, the
attempts, their challenges and the reason each failed. The verifier log is
empty; only the adversary's own reads against H follow. The ideal side's
`fail` publishes the same `failView` (R1Z/GamesR1.lean:135–136).

## 2. The Rust prover before this change

At 74e78062c, `prove_masked_retrying_with`
(crates/aspis-r1-cost-probe/src/prover.rs:343–361) continues only on
`Error::Rejected`, which only the P_R1 check returns (prover.rs:300–313).
Every other error aborts the loop.

Pole. `host_semantic::build_with_material` draws λ and χ (rows 0 and 1) and
calls `build_pool_v1_pair_forest_copy_helper_v1`
(crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs:171–179),
which computes the copy rows and then `build_copy_logup_helper`
(crates/aspis-statement/src/logup.rs:192–224). That function returns
`LogUpError::ActivePole { row, side }` when χ equals a value whose weight is
nonzero. The builder collapses this to `PoolV1PairTraceErrorV1::CopyImbalance`,
the cost probe to `r1_wire::Error::Public`, and the prover to
`Error::Semantic` (prover.rs:172), so the loop aborts.

There is a second difference, smaller than the one D73.4.1 names. Rust's
`build_copy_logup_helper` inverts only slots with nonzero weight. Weights
are not constant: `copy_weight` (pair_forest_trace.rs:593–613) is 0 for the
other variant's links and for the append link on the side not taken at each
level. Lean's `NoPole` checks every slot of every active row, weighted or
not, including unused slots (value 0). So the Rust ActivePole event is a
subset of Lean's `¬NoPole`. On the remainder, where χ equals a zero-weight,
overwritten (§4) or empty slot value, Lean rejects the attempt, while the
Rust loop did not reject it (the helper builds, and the attempt went on to
the P_R1 check).

Mask exhaustion. Both expanders return
`StateOnlyMaskBuildError::MaskSampleExhausted` after 16 failed tries for one
M31 word: `SeedExpander::m31` (crates/aspis-prover/src/state_only_hiding.rs:352–360;
`MASK_SAMPLE_RETRY_LIMIT = 16` at line 48), used by the field-mask
material, and `Profile21SourceExpander::m31`
(crates/aspis-prover/src/state_only_entropy.rs:785–793), used by the D
derivation. These are Lean's two streams (L₁, L₂). The prover maps both to
`Error::Semantic` (prover.rs:141, 145), so the loop aborts. The nonce has
already been reserved at that point (state_only_entropy.rs:408).

All N fail. After 8 rejections the loop returns `Err(AttemptsExhausted)` and
no proof bytes (prover.rs:360).

## 3. Lean against the D38.3 plan

D38.3 says: a capped loop with N = 8, `AttemptsExhausted` publishing nothing,
fresh OS secrets per attempt with the nonce burned first, and rejected
challenges never logged. It does not mention poles or mask exhaustion; D40.3
added the pole as a rejected attempt and D73.4.1 confirmed that.

- Pole: Lean and D40.3/D73.4.1 agree. No conflict.
- Mask exhaustion within an attempt: Lean rejects and continues. D38.3 is
  silent, so nothing contradicts Lean. The "any other error aborts" rule at
  prover.rs:341 was the R-retry worker's addition, not part of D38.3.
- All N fail: Lean publishes the fixed `failView`; D38.3 says nothing is
  published. I read these as the same thing. `failView` is a constant of the
  wire, carries no attempt data, and has an empty verifier log, so the
  observable outcome is one fixed value. A Rust `Err(AttemptsExhausted)` with
  no bytes is one fixed value too. The correspondence note cherry-picked with
  D73 records this reading (CORRESPONDENCE-G-SIM.txt lines 102–104: "the R-retry convention, not a
  simulator difference"). Because the two descriptions do not differ in
  substance, I did not stop on this point. If the lead requires an actual
  `failView` byte string on exhaustion, that is a protocol choice for the
  lead and it is not made here.

So the change made Rust follow Lean on all three points, and no item had
to stop.

## 4. The change

Only four files in `crates/aspis-r1-cost-probe/src` change. Nothing under
`crates/aspis-statement`, `crates/aspis-prover` or `refine/` is touched, so
the D70 writer path and its gates are unaffected. The pole is detected in
the cost probe from public aspis-statement functions instead of changing
the aspis-statement builder.

- `host_semantic::no_pole` (feature `r1p-check`) implements Lean `NoPole`.
  After λ and χ are drawn and before the helper is built, it checks χ
  against all four slot values of every copy-active row. Only a verdict bit
  leaves it, and the loop has no early exit. If it fails, `build_with_material`
  returns `r1_wire::Error::ActivePole`. That variant is unit, carries no
  detail, and exists only under `r1p-check`.
- `host_semantic::lean_copy_row_values` computes Lean's `copyRowValues`:
  for each registry endpoint, `compress_tagged_tuple(tag, tuple, λ)` is
  added at its static slot (its position among the registry endpoints on
  the same row and side), and weights are ignored. The tuple read copies
  `tuple_value` (pair_forest_trace.rs:580–591), which is private. The
  prover's `pool_v1_pair_forest_copy_rows_v1` cannot be used. It puts an
  endpoint in the first slot whose weight is zero, so on a withdrawal the
  PrivateTransferOnly producer at row 523 is overwritten by the next
  endpoint. This was found by a failed host test (evidence-pole.json,
  superseded runs).
- `prover::semantic_error` maps `ActivePole` to `Error::Rejected`.
  `prover::mask_error` maps `MaskSampleExhausted` from either expander to
  `Error::Rejected`. Both mappings apply only under `r1p-check`. Without it
  every error is `Error::Semantic` as before, and other mask errors
  (`ReusedMaskNonce`, `ZeroPrivateEntropy`, `Layout`, `TraceShape`) still
  abort.
- The loop is unchanged. A pole or an exhausted attempt is the same
  detail-free `Rejected` as a failed P_R1 check. It consumes one of the 8
  attempts, its nonce is already burned (the reservation precedes both
  events), its secrets are dropped, nothing is published, and the next
  attempt draws fresh OS secrets. After 8 failures of any mix the result is
  `AttemptsExhausted` with no bytes.
- Test hooks (`cfg(all(test, feature = "r1p-check"))`): `force_poles(&[k])`
  makes `no_pole` false on attempt k, and `force_exhaustion(&[k])` returns
  `MaskSampleExhausted` right after attempt k's reservation.

The verifier build is unchanged in object code. With default features (the
verifier build), the cost-probe lib was built from these sources and from
the base sources, at the same paths. All 9 codegen objects are identical
(sha256 of their concatenation `23e7ecfc…` in both builds). The rlib differs
only in its metadata, which records source-file hashes
(rlib-compare-results.txt). The SBF program itself was not built here. The
`r1_wire.rs` edit keeps every line number, so panic locations do not move.
Under `prover` without `r1p-check`, the new functions return
`Error::Semantic` exactly as the old closures did.

## 5. Tests and evidence

Host run at the committed sources (evidence-pole.json, pole-test-results.txt):
`cargo test --release -p aspis-r1-cost-probe --features r1p-check --lib`,
27 passed, exit 0, wall 3:57.76, peak RSS 506,476 KiB, 0 swaps, in a
MemoryMax 8G / MemorySwapMax 0 scope. These are the 21 tests of D73 and the
following six new ones.

- `pole_on_first_attempt_is_a_rejected_attempt`: attempt 1 hits the pole.
  No P_R1 check runs on it, attempt 2 is published (it carries attempt 2's
  C1 root), there are 2 distinct nonces, field-mask entropies and salt seeds,
  2 durable reservations, and the proof passes strict tx1 + tx2 and dense.
- `pole_on_eighth_attempt_exhausts_and_publishes_nothing`: 7 P_R1
  rejections, then a pole on attempt 8. The result is `AttemptsExhausted`,
  with no ninth attempt, 8 distinct nonces and 8 reservations.
- `mask_exhaustion_on_first_attempt_is_a_rejected_attempt`: attempt 1's mask
  decode is exhausted. Attempt 2 is published and verifies, with 2 nonces
  and 2 reservations.
- `no_pole_is_lean_no_pole_transfer` / `_withdrawal`: a generic χ is clear,
  and χ = 0 is a pole (some active slot is unused). Every active Lean slot
  value is a pole. Every prover copy-row value is a Lean slot value of its
  row and side. A weighted value is also `ActivePole` in
  `build_copy_logup_helper`. The other values are Lean poles that the
  weighted-only builder accepts: 42 distinct nonzero values on the transfer
  fixture and 50 on the withdrawal fixture, plus 0. Before this change,
  the Rust loop did not reject at these χ values, and Lean does.
- `static_slots_are_the_terminal_constants`: for all 136 links, registry
  order, tags, rows and the registry-order slots equal `COPY_LINKS` in
  pair_forest_copy_terminal_constants.rs, the file the Lean
  R0P/CopyConstants.lean transcribes.

The existing retry, exhaustion and freshness tests pass unchanged:
`forced_rejections_then_accept_publish_the_eighth_attempt`,
`eight_rejections_exhaust_and_publish_nothing`,
`real_check_publishes_a_verifying_proof` and
`retry_loop_refuses_non_r1_variants`.

## 6. What remains open

- The correspondence is a reading of the sources, not a refinement proof.
  "Rust no_pole ⇔ Lean VR1" rests on three things. The first is the copied
  tuple read, which is tested only indirectly, through agreement with the
  prover's own row values. The second is Lean `copyLinks` matching
  `COPY_LINKS`, which is the R0P transcription and was not rechecked here.
  The third is `h.build w` being the compiled trace that the helper reads
  (G-ref).
- The SBF verifier program was not rebuilt. Identity is shown for the
  host default-feature objects only.
- There are other per-attempt failures that Lean has no counterpart for and
  that still abort. The Rust QueryScan (`queries_from_pairs`) can return
  `Error::Transcript`, while Lean's `kstarOf` is total. Any `Error::Semantic`
  from mask application, salts or builders also aborts. These are R-wire /
  R-commit matters. Their probability is not bounded here, and they are not
  changed.
- Exhaustion of all 8 attempts is "no bytes" in Rust and `failView` in Lean.
  §3 treats these as the same; if the lead reads them differently, it is the
  lead's ruling to make.
- D73.4.3 (P_chk ⇒ P_R1 premises, the z9e port re-check) and D73.4.4 (tape
  law, inactive-sum and batched formula equality) are untouched.
- ε_pole is unchanged. The Rust pole set is now exactly Lean's `poleSet`
  (at most 4 values per active row, 214 active rows, ≤ 4,096 positions), so
  the D40.3 bound applies as stated.
