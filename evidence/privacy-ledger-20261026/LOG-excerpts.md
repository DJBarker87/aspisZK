<!-- Original LOG.md lines 5356–6526 -->
### Lead acceptance of J0c and `privacy_R1` (2026-10-18); D42: the R1 privacy theorem, conditional on named hypotheses

The worker commits a3c80b748, 4f903c387 and 376423b24 are cherry-picked. The
lead verified every host receipt (SHA matches, exit 0, axioms standard or a
subset, no sorry/axiom/admit/native_decide/overrides):

| Module | Attempt | SHA | Axiom lines | Peak RSS (KiB) |
|---|---|---|---|---|
| R0Z/HvzkV | 3754 | `9b8096b0…` | 21 | |
| R1Z/PoleMassR1 | 3760 | `b7ab6669…` | 11 | 7,202,756 |
| R1Z/ModelsVR1 | 3761 | `cfcf9954…` | 4 | |
| R1Z/MaskImageVR1 | 3762 | `179d2d98…` | 5 | |
| R1Z/PrivacyR1 | 3763 | `9be4fb32…` | 1 | |
| R0Z/HelperInactive | 3765 | `4424b826…` | 5 | |

Attempts 3755 and 3757 hit Lean's -M7000 memory exception. The work was
split into modules, and the failing sources were not rerun. PoleMassR1 peaks
about 137 MB under MemoryMax and must not grow; its Finset elaboration should
be reworked before the final replay.

**D42.1 `privacy_R1`.** It proves `ZK_FSV h (VR1 h) B outputs fs x ε` with

ε = M·q/Umin + (M²/Umin + εexh) + Mi²/Umin + N·4096/Q.

ZK_FSV quantifies over every witness w with h.public w = x.1. The real side
is the honest retrying prover. The simulator `simV` uses the per-challenge
pole-free set VR1. Hypotheses:
- PackField and PublicBase;
- `BuilderSoundOn`, the builder fields baseTyped, lanes, helperSum and
  helperInactive;
- `Sem1Uniform` for every adversary's draw;
- `R1RealModelV` and `R1IdealModelV`.

For N = 8, q = 2^64, M = 8·2^21, Umin = 2^255 and Q = p⁴, the value is
≈ 2^-109, dominated by the pole term. The Lean numeral for that
instantiation was dropped while working around the memory limit (D41's
r1_error_N8 covers the first three terms).

**D42.2 The V-form models (reviewed).** `ModelsVR1` keeps every D41 field
except agreement. Agreement now names the P ∧ no-pole games
(`middleRealAbortV`, `middleIdealAbortV`/`idealTestV`). This is required:
the honest prover accepts on P ∧ V, and the simulator retries on P alone.
The coupling bounds are re-proved as in D41. `hybrid_ideal_le` charges the
difference to `poleBad` (some attempt has P ∧ ¬V), whose mass is at most
N·4096/Q by `pole_mass_le` and the union bound. Accepted.

**D42.3 Sem1Uniform.** This is a new named premise, in upper-bound form: a
λ-indexed family of at most m values is hit by χ = sem 1 with mass at most
m/Q. No existing lemma fixes the FS draw's law (FsGood header; MaskD2's
`uniform_point_mass` is abstract). It joins the ZF1 refinement list, together
with the R1 sampler's correspondence (the spend-path sampler proofs are the
source).

**D42.4 Builder.** `helperInactive` is proved for every trace
(`active_registry`, [propext, Quot.sound]). Still open:
- `helperSum`: CopyRegistry's (row, slot) Nodup facts are the expected
  multiplicity input;
- `lanes`: R0P builder completeness.

**D42.5 R1 privacy status.** The privacy theorem for R1 now exists as one
Lean statement. It is conditional on:
1. P_R1, enforced by the prover through the D38 check (proving that check
   correct is the certificate route of D38.5);
2. the builder fields helperSum and lanes;
3. Sem1Uniform and the R1 real and ideal models: lazy programming, game
   agreement (prover refinement), the freshness tables HitFresh/PairFresh,
   and read counts;
4. the gaps G-root, G-def and G-retry (D41.5);
5. ZF2: `simV` and the choice-based simulator are not efficient;
6. classical ROM only.

No transversality premise remains (D29).

### Lead acceptance of J0d (2026-10-18); D43: helperSum proved; builder obligations reduced to three

The worker commits c2ff53224, 3388ce7c5, ba3fb2797 and 82e9e06e9 are
cherry-picked. The lead verified each host receipt (SHA matches, exit 0,
axioms standard or a subset, no overrides):

| Module | Attempt | SHA | Axiom lines | Peak RSS (KiB) |
|---|---|---|---|---|
| R0Z/HelperSum | 3871 | `8fc3d19f…` | 9 | |
| R0Z/BuilderSound | 3872 | `b6031988…` | 4 | |
| R1Z/PoleMassR1 | 3882 | `72fa96fc…` | 11 | 6,633,196 (was 7,202,756) |
| R1Z/PoleN8 | 3883 | `7eebeadd…` | 3 | 1,695,200 |

Evidence: `t2b2b/evidence-J0d.json`.

**D43.1 helperSum.** `helperSum_of_balance` proves that CopyLinkBalance on a
trace implies ∑ helper = 0 for all λ, χ. It uses CopyRegistry's
producer/consumer slot Nodup facts and keeps `helper`'s own 0⁻¹ = 0
convention. `HonestBuilderCore`, with fields baseTyped, lanes and balance,
gives `HonestBuilderSound` and `BuilderSoundOn` via
`builderSoundOn_of_core`. The builder obligations behind `privacy_R1` are
now exactly three:
- base typing;
- ProductionHolds without Copy;
- CopyLinkBalance of the honest build.

All three are R0P builder completeness.

**D43.2 PoleMassR1 reworked.** Only two proof bodies changed
(`poleSet_card_le`, `poleSet_card_le_4096`). The lead diffed every
declaration header: there are no statement changes. The module now adds
≈54 MB over its imports. Its dependent PrivacyR1 (source unchanged) must be
rebuilt in the final replay.

**D43.3 pole_N8.** `pole_N8_M31` proves 8·4096/p⁴ ≤ 2^-108 symbolically
(`m31_pow4: 2^123 ≤ (2^31−1)^4`). The combined numeric bound
(2^-166 + 2^-108) is not yet stated as one Lean term.

**D43.4 Process.** Attempt 3870 started just after another session's
charon/cargo job had launched, between the gate check and the launch. The
worker then moved the gate into the same SSH command as run2.sh, aborting on
a non-empty gate. That is accepted only as an aborting precondition. The gate
output must still be recorded per attempt.

### Lead acceptance of ZF2 (2026-10-18); D44: an explicit, witness-free simulator for R1

ZF2 (worker aca7598b5..749f9a778, 9 commits, cherry-picked) is accepted.
The design is `zf1/DESIGN-ZF2-SIMULATOR.txt`. The lead verified each host
receipt (SHA matches, exit 0, standard axioms, no sorry/axiom/admit/
native_decide/overrides, no `Classical.choose` in any of the sources):

| Module | Attempt | SHA | Axiom lines |
|---|---|---|---|
| R0Z/HvzkS | 3910 | `877fa7c7…` | 9 |
| R0Z/RefPayload | 3911 | `d7e378fd…` | 17 |
| R1Z/RefCosetR1 | 3912 | `deaffbc8…` | 2 |
| R1Z/SimulatorR1 | 3913 | `b2820559…` | 4 |

**D44.1 The simulator.** `simE π B outputs x ch t = (metadata outputs x
ch, shift x.1 B ch (refPayload x.1 B ch + A π B ch (equiv.symm t)))`. It
takes no instance and no InLanguage proof, and the lead read the definition.
`refPayload` is the zero payload trace's cTilde formula with S₀ added at
`.maskSum`, so it is computed from public data only.

The dummy-witness alternative was checked and rejected: such a view lies in
a different coset, at statistical distance 1, and the verifier's initial
sumcheck test already separates it.

Claim Z (`cTilde_sub_ref_mem_range_R1`): for every valid, base-typed w,
cTilde w − refPayload ∈ range A_ch.

**D44.2 `privacy_R1_eff`.** It proves ZK_FSS against simE with the same error
as `privacy_R1`. The hypotheses are unchanged except that the ideal model is
`R1IdealModelS … (simE …)`. This closes D42.5 item 5 (ZF2) at the level of
Lean statements.

Efficiency is a meta-level reading of the definition and is not formalised.
The axiom line's Classical.choice comes from propDecidable in `if`, not from
choice of a witness. Simulation cost equals the public P_R1 check (22.6 s
measured, D38) plus one payload computation (estimated, not timed).

**D44.3 New item G-sim.** A Rust simE with a host timing, a check that its
output passes the R1 verifier, and the L/O-split correspondence (with
G-ref).

Remaining for R1 privacy (D42.5, updated):
1. P_R1 enforcement: the D38 check and its certificate refinement.
2. Builder completeness: baseTyped, lanes, CopyLinkBalance (D43.1).
3. Sem1Uniform and the R1 real model plus R1IdealModelS, i.e. G-def,
   G-prog and G-ref (in progress).
4. G-root, G-retry, G-sim.
5. Classical ROM only.

### Lead acceptance of the R1 games (2026-10-18); D45: the ideal model is proved; real-side hypotheses narrowed

The R1 games work (worker 4d6ee9980..72f11706a, 12 commits, cherry-picked)
is accepted. The design is `zf1/DESIGN-R1-GAMES.txt` §0–§8. The lead verified
each host receipt (SHA matches, exit 0, standard axioms, no overrides):

| Module | Attempt | SHA | Axiom lines |
|---|---|---|---|
| R1Z/LensR1 | 3951 | `90bc5726…` | 10 |
| R1Z/TranscriptR1 | 3954 | `e8b6f22d…` | 18 |
| R1Z/GamesR1 | 3957 | `630393aa…` | 21 |
| R1Z/PrivacyGamesR1 | 3958 | `ec1a2ede…` | 2 |

**D45.1 The games are defined.** `fsR1` is the real and ideal pair, and
`abR1` is the abort bridge.
- The real game is the honest retrying prover: up to N attempts with
  independent secrets, accepting on P_R1 ∧ VR1 ∧ ¬exhausted. A rejected
  attempt publishes nothing; if every attempt fails, a fixed failure view is
  published.
- The ideal game is the same loop on P alone, with simE (or simV), answering
  from the table programmed at the published addresses.

**D45.2 G-root is closed at the model level.** It was checked against
verifier.rs and r1_semantic.rs. Every root, opened salt and path digest is in
the input or is the answer to a verifier read (115 transcript reads, plus one
leaf read and 6 node reads per query and tree). So proof = f(view, verifier
log), and `extend` puts that log at the front of observerOracle.

**D45.3 What is proved.**
- `R1IdealModelS` (simE) and `R1IdealModelV`, every field. The coupling is
  the identity, so Mi = 0 and ε_prog = 0. The programming collisions are
  charged inside the real side's M²/Umin.
- `R1RealModelV`:
  - the read count M = N·(115 + Mc), with `card_TRead = 115` proved;
  - transcript HitFresh;
  - PairFresh for transcript×transcript pairs and transcript×commitment
    pairs (the latter via `CmLayout.cross`).
- `privacy_R1_games` is privacy_R1_eff on the concrete games, with error
  N(115+Mc)·q/2^255 + (N(115+Mc))²/2^255 + εexh + N·4096/Q. The N = 8
  numeral is not compiled. It is expected to stay pole-dominated, ≈ 2^-108.

**D45.4 What remains a hypothesis.** These are fields of `R1RealData`, per
adversary and witness:
- `cp`: the lazy-programming coupling (G-prog);
- `Agree`: real and middle games agree outside the events (G-ref);
- `CmLayout`: hit, pair and cross for the salt, leaf, node, expander and
  seed reads;
- exhaustion mass ≤ εexh (G-exh);
- Mc: the commitment-read count, counted from Rust only.

These are also unchanged: Sem1Uniform, BuilderSoundOn (baseTyped, lanes,
CopyLinkBalance), PublicBase, and classical ROM only.

**D45.5 Rust ↔ Lean refinement list (design §6.4).**
- R-wire: framing, decoders, QueryScan, Merkle-path reads.
- R-ser: proof bytes = serialize(view, log).
- R-commit: prover.rs commitment phase and salted trees.
- R-causal: row i depends only on earlier challenges.
- R-retry: the retry loop in the Rust prover.
- R-pub: the Rust P_R1 check (D38.5 certificates).

**D45.6 Process.** The worker gated on Lean processes only, as instructed.
Spend-path cargo and charon jobs ran concurrently at times without incident.

### Lead acceptance of builder completeness (2026-10-19); D46: the builder is a refinement premise

Worker a46873ead..cf81ffd86, cherry-picked. `R0Z/BuilderComplete.lean`, host
4063 (in-window `run2-par.sh`): exit 0, 3.68 s, 6,616,004 KiB, 0 swaps.
SHA verified by the lead; standard axioms. Evidence:
`t2b2b/evidence-builder-complete.json`. Design:
`t2b2b/DESIGN-BUILDER-COMPLETE.txt`.

**D46.1 Inventory.** No concrete honest builder exists in Lean, here or on the
spend path.
- `HonestProver.build` is a field left deliberately uninstantiated
  (ZkStatement.lean:302–308).
- R0P and the spend path only extract from a trace: ProductionHolds,
  `lanes_zero_iff_holds`, CopyLinkBalance, `input_note_extracted`, and
  Rspend/extract.
- The builder exists only in Rust: the `compile_pool_v1_pair_forest_*`
  functions, then `host_semantic::build_with_material`.

**D46.2 Proved.**
- `lanes_iff_nonCopy`: for a base-typed trace and |K| > 4096, `lanes` is
  equivalent to `NonCopyHolds`, the seven families that read neither λ, χ nor
  column 26. The proof uses a pole-free χ obtained by counting.
- `baseTyped_ofColumns`: any `ofColumns` builder is base-typed by
  construction.
- `honestProverOf S Rel transport`.
- `builderSoundOn_of_refines`: BuilderRefines + |K| + PublicBase ⇒
  BuilderSoundOn.
- `inputNoteExtracted_of_refines`: a sanity check that the premise is the
  trace-side image of the payment relation that soundness extracts.

**D46.3 The premise.** `BuilderRefines S Rel` has two fields:
- `nonCopy`: NonCopyHolds of the honest build;
- `balance`: CopyLinkBalance of the honest build.

This is the builder's correctness against the Rust prover. It is a refinement
obligation of the same kind as the soundness side's source correspondence,
and nothing more follows from Rspend while the builder is abstract.

Ways to discharge it:
- a Lean model of the legacy builder (relocate_and_extend, the bank merge)
  with an Aeneas refinement of the Rust; or
- a per-build certificate the prover checks before publishing. Rust already
  checks the 18,089 transfer residuals at runtime (`finish`,
  pool_v1_pair_forest_honest.rs:80). A check-and-retry is witness-dependent,
  however, so as a privacy argument it would need a failure-mass bound like
  ε_pole. The lead's preference is the Lean model.

Instantiating W := Wspend and Rel := Rspend waits for the build integration.

### Lead acceptance of Sem1Uniform for R1 (2026-10-19); D47

The worker commits 36760a048, 9a9921af2 and eb4690a1b are cherry-picked.
Host attempts 4164, 4165 and 4166 ran in-window (slot 1). The lead verified
each (SHA matches, exit 0, standard axioms, no overrides). Attempts
4160–4163 were elaboration failures, each with a changed source. Evidence:
`zf1/sem1-uniform-evidence.json`.

**D47.1 Proved.**
- `sem1Uniform_abR1`: `Sem1Uniform ((abR1 W N hN).draw adv x) (p⁴ − 1)`
  for every adversary and statement, with no additive term.
- The exact form is `sem1_mass_le_exact` ≤ m·(⌊2^256/p⁴⌋+1)/2^256. The bias
  is multiplicative and ≈ 2^-132. Q = p⁴ − 1 is the best natural number.
- In abR1 the row-1 answer is its own uniform coin coordinate, so address
  repeats do not arise here. They stay charged to ε_coll in the real-to-middle
  coupling.
- `pole_N8_M31_pred`: 8·4096/(p⁴−1) ≤ 2^-108.
- `privacy_R1_games_sampler` is `privacy_R1_games` with `hdraw` discharged.
  Landed statements are unchanged.

**D47.2 Remaining premises (R-wire).**
- `SemRows01 W`: χ = sem 1 is `s1` of the row-1 answer, and sem 0 does not
  read it. This matches r1_wire.rs `begin`.
- `QM31SamplerLaw s1`: rank is a bijection onto Fin 2^256, emb is injective
  below p⁴, and s1 b = emb(rank b mod p⁴). It is restated from the spend
  path's proved sampler facts, which are pinned at 36353e178:
  - ExtractedQM31SamplerCorrect.sample_total;
  - qm31Digits_value;
  - SourceSamplerByteRank.rank;
  - sampled_decode_eq_iff.

The carrier transports (Array U8 32 ↔ Fin 32 → UInt8, and QM31 ↔ K) are the
open link. They join the build-integration job.

### Lead acceptance of G-prog/G-exh/G-count (2026-10-19); D48: commit interface corrected to phase-indexed roots

The worker commits 85307cedc and 30886c9d8 are cherry-picked. Host attempts
4002 (`R1Z/LazyTable`) and 4004 (`R1Z/CommitReadsR1`) ran in-window. The lead
verified both: SHA matches, exit 0, standard axioms. Evidence:
`zf1/r1-real-evidence.json`.

**D48.1 Proved.**
- Generic lazy programming: `mean_prog`, `prog_first`/`prog_off`, and
  `run_eq` (the middle game equals the programmed table on pairwise-distinct
  causal reads).
- Exhaustion: the M31 rejection loop rejects exactly 2 of 2^32 words, and
  εexh ≤ N/2^476 under `RCommitCount`.
- Read count: Mc = 1,685,214 + E₁ + E₂, and 115 + Mc ≤ 2^21.

Correction: the folded tree has 2^18 leaves, not 2^16 as the couplings
design said.

New R-commit premise `RCommitCount`: stream 1 has at most 45,056 limbs, which
assumes at most 26·1024 relation-free mask cells (to be confirmed from
aspis-statement); stream 2 has 4,096 limbs.

**D48.2 Modelling error found in the landed GamesR1.**
`R1Prover.commit` returns all three roots before the transcript. In Rust:
- the C2 root depends on rows 0–1, because its leaves include
  h1 = helper(λ, χ) (host_semantic.rs);
- the folded root depends on rows ≤ 29, since it is built over
  fold(q, α0) after α0 (prover.rs).

An R-commit premise equating `commit` with the Rust phase would therefore be
false, and `privacy_R1_games'` would be vacuous for the real prover. This
does not affect the landed theorems' truth: they hold for any `R1Prover`. It
affects only whether the Rust prover is an instance.

**D48.3 Lead decision: phase-indexed commitments.** Do not edit the landed
GamesR1. New modules define `R1ProverP`, with commit of type
`Challenges K → Fin 3 → OracleAnswer`:
- the C1 root is constant;
- the C2 root depends only on rows 0–1;
- the folded root depends only on rows ≤ 29.

These causality conditions are fields. Commitment reads and the exhaustion
flag are indexed the same way. `realAttempt.step` evaluates the roots at the
partial challenges, and R-causal covers them. The new games `fsR1P`/`abR1P`
reuse the ideal models and transcript freshness, which are unaffected because
the roots there are coins. Then `cp` follows from LazyTable with the
commitment reads in the causal read list, followed by CmLayout, Agree and
`privacy_R1_games'` on fsR1P.

The P_R1 check is unaffected: it reads challenges and public constants only,
not roots.

### Lead acceptance of the P_R1 certificate checker (2026-10-19); D49

The worker commits f38410320..80723cd38 (15) are cherry-picked. Design:
`zf1/DESIGN-P-CERT.txt` §0–§7. The lead verified both host receipts:
- `R1Z/CertSound`: attempt 4121, 20 standard axiom lines;
- `R1Z/CertR1`: attempt 4122, 7 standard axiom lines.

Both ran in-window, exited 0, have matching SHAs and no overrides. Attempt
4120 failed on missing imports.

**D49.1 Proved.** Generic certificate soundness:
- preimage certificates give the inclusions;
- the echelon certificate gives ker Rel ≤ span{n_f}, and hence the BCondG
  shape (no inverse of U needed);
- a right inverse gives the lift shape.

Each is decidable. At the exact P_R1 types: `qprime_of_cert`,
`bcondG_of_cert`, `c1lift_of_cert`, `h1lift_of_cert`, `halfOK_of_cert`,
`queryCard_of_cert` and `p_r1_of_cert`. These are relative to the
row-formula premises rf_own, rf_round, rf_bat, rf_src, rf_chain, rf_rel,
rf_obs and rf_dec, which subsume the D34.3 items.

**D49.2 Measured.** The Rust prototype `z4/z9c.rs` was run on the nuc in a
capped scope:
- A/J, actual or random queries: emit 11.9–12.6 s, check 2.56–2.65 s,
  14.2–14.4 MB certificate, 194–250 MB peak;
- coset: 9.2 s emit, 1.6 s check, 9.8 MB.

Emit plus check is about 15 s, which is cheaper than the 22.6 s eliminating
check. This replaces D38.2's "roughly doubled" estimate, so the prover-latency
cost of D29 is about 15 s per attempt with the current code. Ranks match
z9b, and 8/8 corrupted certificates were rejected at their intended steps.

On structure B the checker fails closed at the first C1 lift (rank
100 < 112), which is acceptable because a false negative only costs an
attempt. Whether C1Lift itself fails on B is not computed.

**D49.3 Enforced predicate.** P_chk := (emit succeeds ∧ check passes). It
transfers to `maskImageOn_R1` by antitonicity once `check_sound` is composed.

**D49.4 Open.**
- C2: the rf_* premises, including the Z4c round-coordinate map.
- C3: Aeneas extraction of the checker only. The constraints are u32/u64
  with proved bounds, flat Vec, plain while loops, monomorphic code, and one
  loop nest per function.
- `check_sound` composition.
- Prover integration, and timing on a second machine.

CertR1 peaks 0.27 GB under -M7000; wider importers must split. A Freivalds
check was rejected (§7.3).

### Lead acceptance of the builder model (2026-10-19); D50: Rspend strengthened by the change sentinel for privacy

The worker commits 23f5bd8cd..6d5a2889b (14) are cherry-picked. The design is
`t2b2b/DESIGN-BUILDER-MODEL.txt` §1–§7. The lead verified the six host
receipts:

| Module | Attempt |
|---|---|
| BuilderModel | 4201 |
| BuilderModelAux | 4204 |
| BuilderModelHash | 4208 |
| BuilderModelDigest | 4210 |
| BuilderModelSentinel | 4211 |
| BuilderModelBridge | 4212 |

All exited 0, ran in-window (slots 1 and 2), have matching SHAs and standard
axioms, and contain no overrides. The failed attempts were elaboration
errors, each followed by a changed source. Two whnf/simp timeouts were fixed
with local irreducibility; no limits were raised.

**D50.1 Proved.** `buildModel` is a staged Lean model of the Rust builder,
and all seven NonCopyHolds families hold for it (`nonCopy_model`):
- Poseidon holds by construction;
- schedule and path need no premise;
- value, occupancy, asset and digest hold under named witness premises.

**D50.2 Finding: no builder can satisfy `BuilderRefines S Rspend`.**
`refines_forces_sentinel` (lead-read): for any builder, BuilderRefines on a
private transfer forces `pub.change 7 ≠ 0`. Copy link 1124073492 places the
change digest on occupancy row 1018, whose sentinel equation requires it.
Rspend has no such clause, while the Rust builder already rejects a zero
sentinel with a salt retry (`two_outputs`).

**Lead decision.** The privacy relation is Rspend⁺ := Rspend ∧ (transfer →
change[7] ≠ 0). The soundness theorem continues to extract Rspend. This is
consistent, because the honest prover proves a subset of the relation that
soundness extracts.

On privacy, the salt retry conditions the change commitment (a public
statement value, a hash output in the ROM) on one limb being nonzero. That
affects the commitment's own hiding, which is outside this ZK theorem, by
at most the conditioning on a ≈2^-31 event, not the view given the
statement. This is recorded as an item for the note-commitment hiding
argument and is not checked here.

A soundness-side opportunity (not required): since accepted proofs force the
sentinel, the extracted relation could carry it too.

**D50.3 Modelling choices the Rust refinement must justify.**
- Block rows are defined by the canonical Poseidon transition. This moves the
  open raw-limb boundary to the builder side.
- Empty-root siblings come from the frozen table.
- Path aux levels are written from the node inputs.
- The model is total, with Rust's checks as premises.

**D50.4 Open, with the worker's estimates.**
- CopyLinkBalance of the model, 136 links: 3–5 days.
- BaseTyped of the model: about 1 day.
- Rspend⁺ → the model premises, after build integration: 2–3 days. This needs
  model digests equal to the spend path's noteCommitment, nodeCompress and
  pathPrefix.
- Aeneas refinement via extraction-friendly copies of each writer, checked
  by differential tests:
  - value, occupancy, path, merge: 2–3 days;
  - sponge and node: 2 days;
  - Poseidon: 1–2 weeks. This is the hardest item, and it has failed
    extraction before.

### Lead acceptance of builderRefines_model (2026-10-19); D51

The worker commits 69706d6bf..ffdc53471 (12) are cherry-picked. The lead
verified the nine green host receipts (attempts 4216, 4219, 4222–4225,
4228, 4229 and 4231): SHAs match, all exited 0 in-window, standard axioms,
no overrides. Evidence: `t2b2b/evidence-builder-model-2.json`. Design: §8 of
`t2b2b/DESIGN-BUILDER-MODEL.txt`.

**D51.1 Proved.**
- `buildModel_mem`, i.e. BaseTyped of the model.
- `balance_model`: CopyLinkBalance over all 136 links. It is generated by
  `copy-gen/gen_copy_links.py.txt`, which reads CopyConstants.lean, aborts on
  any kind mismatch, has a `--check` mode, and emits only named lemma
  applications. `decide` appears only on numeral bounds and row equations,
  and `rfl` only on weight literals.
- `builderRefines_model : BuilderRefines (buildModelSpec F) (ModelRel F)`.
- `builderSoundOn_model`, for characteristic 2^31−1.

So the builder premise of `privacy_R1` is a theorem about the model. What
remains is that the Rust builder refines the model, and the map from Rspend⁺
to ModelRel.

**D51.2 ModelRel** is what a later job derives from Rspend⁺ after build
integration. Its fields:
- pubBase and witBase;
- aux: conservation, pair-leaf validity, spendability, the D50 sentinel and
  the withdrawal amount;
- digest: anchor, nullifier, recipient, change, next root and carry, each
  equal to the model's digests;
- pairRight: the input pair's second commitment is the pair node's right
  child. This is the only new witness premise the links needed.

**D51.3 Violation.** Attempt 4218 re-sent 4217's source unchanged: the SHAs
are identical and it exited 1. A local edit script failed before launch.
This breaks the never-rerun-unchanged rule. It is recorded in the evidence,
and the worker's launcher now refuses a source hash it has already sent.
That guard is adopted for all workers.

### Lead acceptance of the phase-indexed real games (2026-10-19); D52: privacy_R1_games′

The worker commits 142b9fa15..99b6f9149 (17) are cherry-picked; GamesR1 is
untouched. The design is `zf1/DESIGN-R1-REAL.txt` §1–§7. The lead verified
all 15 green host receipts (4007 … 4049): SHAs match, all exited 0
in-window, standard axioms, no overrides. Notes on the failed attempts:
- 4005 is void: another worker's leftover launcher in the shared scratchpad
  ran, compiled nothing, and the worker switched to a private launcher.
- 4033 hit the default heartbeat limit and was fixed by restructuring, not by
  an override.

**D52.1 Proved.**
- `R1ProverP` with phase-indexed roots (D48.3). Each attempt is one causal
  read program run on partial answer vectors.
- cp: the frozen-set lazy-programming law (`LazyFrozen`), with
  H(public_bytes) as the frozen address, and `cpP`.
- CmLayout: the byte grammar `gram` for every commitment read, and hit,
  pair and cross freshness for all N·|Pos1| positions. `hidden` shows the
  opening log does not move on unopened reads.
- Agree: `agreeP`.
- exh: εexh = N·16(L₁+L₂)/2^496 + N·|Pos1|/2^255.
- `privacy_R1_games′` on fsR1P/abR1P against simE. The error is
  M·q/2^255 + M²/2^255 + εexh + N·4096/(p⁴−1), with M = N·|Pos1|.

Every field of R1RealData is discharged.

**D52.2 Hypotheses of privacy_R1_games′.**
- PackField, PublicBase, BuilderSoundOn (theorem for the model, D51),
  SemRows01 and QM31SamplerLaw.
- R-rom: `RomModel W`, `RAddrIn`.
- R-causal: `RCausal`.
- R-commit:
  - `RCommitBytes` (the node, leaf, salt, seed, binding and expander
    grammars);
  - `hfib`;
  - `RExh`;
  - E bounds, and 16L ≤ 8E.
- R-wire: `eCm`, `ROpen`, `RComLog`.

Every one of these is a statement about the Rust prover's behaviour, which
is what the refinement work discharges.

**D52.3 Modelling choices (reviewed).**
- The mask nonce is secret. It is never in the proof bytes or read by the
  verifier, per r1_wire.rs, which overrides the "public" context comment.
- The binding read is memoized: the Rust recomputes it at the same address.
- The real game runs all N attempts and charges every read. That is
  conservative.
- The cell bound ≤ 26·1024 (RCommitCount) still needs confirming from
  aspis-statement.

**D52.4 Open.**
- R-ser, R-retry, R-pub.
- Completeness of the read list, i.e. no other hash call in the commitment
  phase.
- The Rust-side discharge of every premise in D52.2.
- An LE byte-formula lemma for `wordsE`.
- The N = 8 numeral.

### Lead acceptance of the rf_* premises (2026-10-19); D53: P_R1 from the checker's tests

The worker commits e899fcdd6..c61320358 are cherry-picked. The lead verified
the 12 green host receipts (4281, 4282, 4287, 4289, 4290, 4294, 4296, 4297,
4299, 4300, 4302 and 4303): SHAs match, all exited 0 in-window, standard
axioms, no overrides. Evidence: `zf1/rf-evidence.json`, 24 attempts. The
failures were memory and recursion blowups and naming errors; none was rerun
unchanged and no cap was raised. 4296 had finished green before the
session-limit cut, and was recorded without a relaunch.

**D53.1 Proved.** On the Lean side, all eight rf_* premises are discharged:
- RF-dec: the decode8 limb order;
- RF-src: Rust-built sources lie in Gonly, Vsem and Ph1;
- RF-chain: ChainT0K4 lies in the span of the Rust chain_targets under SemK4;
- RF-round;
- RF-own: ownMap equals the Rust raw_c columns, with the 12-lane limb
  layout;
- RF-obs/RF-col;
- RF-bat/RF-rel: the wflat order, and B0R1′ ≤ ιb(ker Rel).

D34.3 items 1 and 2 are proved on the Lean side: `storedFirstLineX18` =
the Rust line_node formula; lineInverse = the QueryGeometry multipliers; and
line_fold_with_inverses = lineFoldLinear.

`p_r1_of_checks` derives P_R1 from the checker's tests (PreOK, PreOK₂,
EchOK, RinvOK, half-inverse, limb/length). Its remaining hypotheses are not
row formulas:
- the circle points lie in K₄;
- wb is an F-basis of K;
- the opened folded-cell list covers the open cells;
- one-index side conditions on the selected lift sources.

**D53.2 Moved to C3 (Rust side).**
- The round, batched and relation matrices, and some own columns, are
  defined as the Lean maps' coordinates. C3 must show the Rust builders
  round_row/tail_row, unit_functionals and design_relations/
  limb_functionals compute them. The other columns already have Lean closed
  forms matching the Rust.
- D34.3 item 3 (`ell` versus Rust weight kinds 5/6).
- π versus the Rust transport table, `natural` versus naturalLineValue, the
  stored points, and batch inversion.
- check_sound, i.e. extracting the checker and composing it with
  p_r1_of_checks.

### Lead acceptance of the first builder refinement (2026-10-19); D54

The worker commits 8288078b9..6a655b053 (13) are cherry-picked. The lead
verified the 11 green host receipts (4233, 4235, 4238, 4241, 4246, 4248,
4253, 4257, 4258, 4260 and 4262): SHAs match, all exited 0 in-window,
standard axioms, no overrides. Attempt 4237 (exit 1) was checked after the
session-limit cut, and nothing was resent unchanged. Design:
`t2b2b/DESIGN-BUILDER-MODEL.txt` §9.

**D54.1 Proved, for the value, occupancy, path-aux and merge writers.**
- Extraction-friendly Rust copies are in `refine/writers`.
- Native differential tests against production (read-only from the spend
  branch at 0c46bf447): 200k value, 100k occupancy, 52k path and 1M
  node_right cases; 2k merge shape violations; the 2 saved fixtures; and 256
  randomized full honest compiles.
- Extraction with pinned Charon cb50ff16 and Aeneas b59d5188.
- In Lean:
  - `aux_block_model`: write_aux_block equals model block 63;
  - `path_block_model`: rows 912..1007;
  - `merge_model`.

Loops are handled by induction; nothing is evaluated.

**D54.2 Lead rulings.**
- **B1 accepted.** `import Aeneas` is replaced by `import Aeneas.Std` and
  `import Aeneas.Tactic.RustAttributes` in the generated file, and the edit
  is asserted by `refine/extract/substitute.py.txt`. The full `Aeneas` root
  does not build unpatched under 4.32 in this tree. Build integration must
  reconcile this Aeneas.Std with the spend path's ported one: two versions
  cannot coexist in one tree.
- **B2 accepted.** The generated `maxHeartbeats`/`maxRecDepth` lines are
  deleted, which is stricter than generated, and the code compiles without
  them.

**D54.3 Open.**
- `node_right_lane7` and the path read-back are checked by differential test
  only.
- ValueLifts, OccLifts and PathLifts are premises. They need the
  Wspend-to-Rust-witness map and the Poseidon/node refinement.
- The merge is proved against an abstract table.
- The copy-to-production link is a differential test, not a proof. The
  production writers use Vec, closures and M31 methods the pinned extractor
  does not handle. The options are a production-source migration (as with
  Decision 1 on the verifier) or accepting tested equivalence.

### Lead acceptance of the sponge/node refinement (2026-10-19); D55

The worker commits d66998036..efd49c19f (9) are cherry-picked. The lead
verified the 7 green host receipts (4263, 4266, 4268, 4271, 4272, 4275 and
4277): SHAs match, all exited 0 in-window, standard axioms, no overrides.
Design: §10 of `t2b2b/DESIGN-BUILDER-MODEL.txt`.

**D55.1 Proved.** The Poseidon permutation is kept abstract through the
plug-in premise `RoundsOk rounds B`: the eleven odd-round outputs lift to the
model's block iterates.
- `block_model`: write_block equals blockCell.
- `node_model`: write_node equals the model's nodeIn block.
- `m31_add_spec`/`m31_sub_spec_wide`, for all canonical inputs.
- `sponge_model`: the full sponge, given the initial state, the absorptions,
  chaining and RoundsOk.
- `note_sponge_model`: the note blocks 1–3, 27–29 and 30–32.

B3 is closed in Lean:
- `node_right_lane7_lift`: the large tweak.
- `read_back_node`: at the copy level. The production relocation still
  links to the copy by differential test.

Differential tests against production were run with `rounds` from the
production permutation:
- 1M M31 add/sub pairs;
- 20k write_permutation, 20k node/forest-node and 20k sponge cases;
- 3,648 full blocks.

**D55.2 Open.**
- Instantiating the owner and nullifier sponges and the tree/append node
  blocks. These are mechanical, by the same pattern.
- `RoundsOk` for the Rust permutation: the Poseidon job.
- The input lifts (Wspend → Rust witness).
- The copy-to-production link (D54.3).

### Lead acceptance of the block assembly and the Poseidon round lemmas (2026-10-19); D56

The worker commits after 1b56fef13 are cherry-picked. The lead verified the
green host receipts (4400, 4401, 4404, 4406 and 4407): SHAs match, all
exited 0 in-window, standard axioms, no overrides. Attempts 4402, 4403 and
4405 were local elaboration fixes. Design: §11 of
`t2b2b/DESIGN-BUILDER-MODEL.txt`.

**D56.1 Proved.**
- `builder_blocks_model`: all 57 Rust-written blocks equal buildModel, under
  RoundsOk, the input lifts and the copy↔production links. Discharge lemmas
  cover chaining, absorptions, node children and digests. RoundsOk is the
  only Poseidon obligation left for the block region.
- `full_round_lift`: an extracted full round equals R0P
  `poseidonFullRound` for every u32 state. No canonicity hypothesis is
  needed: the u64 reductions mod p never overflow.
- `internal_round_lift`: the same for an internal round, matched to R0P's
  ordered foldl through a general ofFn/range′ lemma.
- `PoseidonTables`: INTERNAL_SHIFTS satisfies ShiftsBound/ShiftsOk with
  small numerals only.

Differential tests (diff-g):
- perm_rounds equals the production odd-round outputs on 100k states and on
  all 1,824 blocks of 32 traces;
- the final state equals production `permute` on 50k states;
- m31 add/mul agree on 1M pairs.

The extraction needed no adapter. This is the first time Poseidon has
extracted and its rounds have been proved; the spend path's earlier attempts
stopped at the external wrapper and round composition.

**D56.2 Remaining for RoundsOk.**
1. Generated per-row constant-lift lemmas for EXTERNAL_INITIAL/FINAL and
   INTERNAL, going through `Nat.cast_ofNat` without unfolding large literals.
2. `apply_round_lift` and `leading_pair_lift`.
3. A `perm_rounds` loop invariant, giving RoundsOk for the copy's output.

The copy↔production link stays a differential test (D54.3).

### Lead acceptance of C3: the extracted P_R1 checker (2026-10-19); D57

The worker commits 54f39d467..4f5496ea4 are cherry-picked. The consistent
chain is CertCheckExtracted (4345), then 4363–4373: CertCheckBase … Top,
CertData/2, CertCheckData, CertCheckSound and CertCheckSoundAll. These are
dependency replays: Base and Dot had originally been built against the 4341
extraction. The lead verified all eleven (SHAs match, exit 0, standard
axioms) and checked that no source contains sorry, admit, native_decide or
an override. The replays used the global lock, the caps were not raised,
and CertCheckSoundAll peaked at 7.15 GB, near the cap. The launcher now tags
deliberate dependency replays (`DEPREPLAY=1`).

**D57.1 Proved.** `check_sound`: if the extracted Rust `check pb c` returns
`ok true`, then P_R1 holds on the decoded record. The Rust checker in
`c3/check`:
- is no_std, monomorphic, with checked u32/u64 arithmetic, one loop per
  function and branch-free bodies;
- verifies every certificate-supplied intermediate by plain equality.

Differential test: same verdicts as z9c on the five configurations and the
8 corruptions, and 6/6 corruptions of the new fields rejected. It takes about
8.8 s per check, so the prover-side check is now ≈ 12.6 s emit + 8.8 s check
per attempt, before optimisation.

**D57.2 Hypotheses of check_sound.**
- The builder identifications hOwn, hRound, hChain, hRel, hGOwn, hGRound,
  hGBat, hC1 and hH1. These carry the D53.2 items: `ell` against weight kinds
  5/6, π against the transport table, `natural`, the stored points and batch
  inversion.
- Decoder facts: hhalf, hup, hnq, hz, the lane layouts stO/stG, and φ.
- From p_r1_of_checks: wb, hcov, hsel1/hselH.

The checker reads values mod P, so it also accepts non-canonical
certificates. That is sound, but the differential test does not cover it.

**D57.3 Next.** Extract the column builders (raw_c, round_row/tail_row,
unit_functionals, design_relations/limb_functionals, normalize_d) to
discharge the builder identifications, and integrate the checker into the R1
prover (D38.3).

### Lead acceptance of RoundsOk for the Poseidon copy (2026-10-19); D58

The worker commits dc98360df, 928e057e2, 0bac06653 and f1ef3e481 are
cherry-picked. The lead verified host attempts 4408, 4409 and 4410 (SHAs
match, exit 0 in-window, standard axioms). No source contains sorry, admit,
native_decide, an override, decide or norm_num.

**D58.1 Proved.**
- `PoseidonConstLift`, generated. The generator reads production
  poseidon2.rs, the copy, the extracted Lean and R0P PoseidonConstants.lean,
  and aborts on any disagreement. Its tamper test is recorded: two injected
  value changes aborted with exit 2, and a tampered output failed --check
  with exit 1. All 142 lanes are proved by named steps; no large literal is
  unfolded.
- `apply_round_lift` (all 22 rounds) and `leading_pair_lift`.
- `perm_rounds_lift`, by loop invariant: RoundsOk holds for the copy's
  permutation.
- `builder_blocks_model_copy`: under `BuilderInputLifts`, the old lifts
  without RoundsOk, all 57 Rust-copy blocks equal buildModel.

**The Poseidon obligation of the builder is closed for the copy.** The
copy↔production link is the diff-g differential test (100k states and 1,824
compiled blocks), with the same standing as the other writers (D54.3).

**D58.2 Remaining builder items.**
- Sponge pre-state chaining, which is short with RoundsOk now proved.
- Linking BuilderInputLifts to the witness-level writer outputs, and the map
  from Wspend⁺ to the Rust witness.
- The copy↔production decision (D54.3): migrate the production prover
  writers to the extracted copies, or accept tested equivalence. To be put
  to the user.

### Lead acceptance of the first column builder (2026-10-19); D59

The worker commits 2660e7a5f..c681d4634 are cherry-picked. The lead verified
the 8 green host receipts (4374, 4376, 4377, 4378, 4381, 4385, 4388 and
4391): SHAs match, exit 0, standard axioms, no overrides. The 10 failed
attempts all had changed sources.

**D59.1 Proved.** The chain-target builder `fill_tq` has an extracted Rust
copy. Its differential test matches z9c's chain_targets on all 1,175,056
entries in each of five configurations, and the checker verdicts are
unchanged. On the Lean side:
- the QM31 layer (CertBuildBase/Tower) shows the extracted QM31 product is
  the product in K, under the premise `Tower B` (i² = −1, u² = 2 + i);
- `chain_ident` shows the builder output under φ equals Lean's chainTarget.

`check_sound′` removes hChain and hhalf. In their place it adds:
- hT, the tower premise;
- hal and ha9, saying the Rust alpha limbs are the raw challenge limbs;
- hbuild, saying the prover filled the target matrix with the extracted
  builder.

CertCheckSound2 peaks at 7.16 GB, near the cap.

**D59.2 Remaining builder identifications.**
- hOwn, hGOwn, hC1, hH1 and hRel (raw_c, design_relations). These need
  copies of eq/points/h_weight/evalrow, `natural` = naturalLineValue, the
  stored points, π against the transport table, inactive against
  copyInactiveRows, and the flatC1/flatO layouts.
- hRound, hGRound and hGBat (round_row/tail_row, unit_functionals). These
  need closed forms for the pure-round coordinates, plus `ell` against weight
  kinds 5/6.

Lead ruling: π, the stored points and the OOD points may be taken as input
arrays under named premises (for example "the input table equals π"), to be
discharged with the transport and sampler refinement.

Housekeeping: the builder extraction reused two host output directories from
the superseded first checker extraction. That is recorded; the accepted
chain does not reference them.

### Lead acceptance of the witness-level Rust-copy builder (2026-10-19); D60

The worker commits 8e3e1e172..f027039ef are cherry-picked. The lead verified
host attempts 4412, 4413, 4415, 4417 and 4419 (SHAs match, exit 0 in-window,
standard axioms). Attempts 4411, 4414, 4416 and 4418 were local fixes.
Design: §12.

**D60.1 Proved.**
- `builder_blocks_model_chain`: sponge pre-states are computed, from
  sponge_init and row 10 of the previous block's perm_rounds.
- `PoseidonCanon`: perm_rounds outputs are canonical.
- `builder_witness_model`: for u32 witness and public records (`RustWitness`,
  `RustPublic`) with the named map `toModel` and premise sets `PubCorr` and
  `WitnessOk`, every extracted component returns ok, and every cell of the
  composed 29×1024 trace lifts to `buildModel pub (toModel W)`.

PathLifts, ValueLifts and both OccLifts are now theorems. `invR` rests on
the named premise `Nat.Prime 2147483647`. It is proved elsewhere in the repo
(AspisV8R15.ExactTowerBase) and joins the build-integration list.

**D60.2 Open.**
- The Lean glue (block order, chunk words, child order, invR, assembly)
  matches pair_trace.rs by inspection only. It needs a differential test.
- The stable/late bank merge is not in the composition yet.
- The Wspend⁺ → RustWitness/ModelWitness map (§12.6): values (transfer vs
  withdrawal), keys and salts, path bits and siblings at levels 0, 1–20 and
  21–23, the public side, the WitnessOk/PubCorr range facts, and the
  primality import.
- The copy↔production link (D54.3).

### Lead acceptance of the merged builder, M31 primality and the glue test (2026-10-19); D61

The worker commits 6cf89c077..106f12df5 are cherry-picked. The lead verified
host attempts 4421 (`M31Prime`) and 4426 (`BuilderWitnessMerged`): SHAs
match, exit 0 in-window, standard axioms. Attempts 4420 and 4422–4425 were
local fixes. Design: §13.

**D61.1 Proved.**
- `m31_prime`, by a Lucas certificate with witness 7 over the factorisation
  of p−1. It uses reduce_mod_char modular powers with no value above p², one
  literal-comparison `decide` per check, and norm_num only on the seven small
  primes.
- `builder_witness_merged`: with the late bank on rows 544–863 and the stable
  bank elsewhere, merge_check returns true, merge returns ok, and every cell
  equals `buildModel pub (toModel W)`. The only premises are PubCorr and
  WitnessOk.

**D61.2 Glue differential test.** Production rejected none of the
inputs. The copy's merged trace equals the production forest compile cell for
cell in columns 0–15, on:
- both saved fixtures;
- 512 randomized honest witnesses.

Columns 16–28 are the model's zero stage-H columns and are not compared.
Each of seven single-field mutations makes 1 to 9,788 cells differ, which
shows the comparison has teeth. The Lean glue and its Rust mirror are
generated from one table (`refine/glue/gen-glue.py.txt`). Its `--check`
requires verbatim Lean text in the proved files, and it rejected two
deliberate edits. The structural functions are mirrored one-to-one and are
covered by the full-trace comparison.

**D61.3 Builder status.** The honest builder, as composed extracted Rust
copies, is proved to produce the model's trace, the model satisfies the
builder premise of `privacy_R1` (D51), and the composition is differentially
equal to production. Remaining:
- the Lean-side Wspend⁺ → RustWitness/RustPublic map (§12.6), after build
  integration. The Rust side of the map is `records` in glue.rs.
- the copy↔production decision (D54.3).

### Lead acceptance of the lift-column builder (2026-10-19); D62

The worker commits a88b52d9e..830d9e275 are cherry-picked. The consistent
chain after re-extraction is:

4392 → 4393 → 4394 → 4395 → 4398 → 4399 → 4460 → 4461 → 4463 → 4464 →
4466 → 4470 → 4473 → 4474 → 4478 → 4479 → 4480

The lead verified all 17 (SHAs match, exit 0 in-window, standard axioms, no
sorry/admit/native_decide/overrides). Eleven failed attempts all had changed
sources.

**D62.1 Proved.** `fill_lo` (C1 and H1 lifts) has an extracted Rust copy.
Its differential test matches z9c's lift matrices on all 342,080 entries in
each of five configurations. On the Lean side:
- the helper values in K (eq, the successor/xor-12 points, h_weight, the
  natural basis, evalrow);
- `natR_eq`: Rust `natural` = naturalLineValue. This is a real lemma, and it
  closes that D53.2 item.
- `c1_entry_ident`/`h1_entry_ident`: every entry is the flatC1/flatH1
  coordinate of `obs`.
- `check_sound″`: hC1 and hH1 are removed.

D59's `check_sound′` had a duplicated binder; it was harmless and is removed
in 4479.

**D62.2 New premises under the D59.2 ruling.**
- htr (input table = π), hzx/hzy (OOD points), hsx/hsy (stored points), hin
  (Rust inactive flags = copyInactiveRows). hin is accepted as a named input
  premise, of the same kind as π.
- hselC/hselHv, hloC/hloH (layout), and hblo (`pb.lo` filled by `fill_lo`).

CertCheckSound3 peaks at 7.17 GB.

**D62.3 Remaining in check_sound″.**
- hOwn and hGOwn: the own-matrix builder and the blockM layout.
- hRel: design_relations/limb_functionals.
- hRound, hGRound and hGBat: pure-round closed forms, and `ell` against
  weight kinds 5/6.
- The decoder facts and the inherited premises.

### Build-integration design and a coherence finding (2026-10-19); D63

The worker on side branch `codex/r1-privacy-build-integration-20261019`
(commit ee17c8c86, based on the 100-bit branch with v8-reference merged)
produced `t2b2b/DESIGN-BUILD-INTEGRATION.txt` and compiled host attempts
4520–4529. The branch is pushed by the lead.

**D63.1 Coherence finding (lead-verified).** Neither host workspace is a
single coherent build.
- Lean loads one object per module name and does not check it against what
  dependents were compiled with.
- The privacy and spend closures share module names with different objects:
  the sampler closures share 28 names, 23 with different objects and 6 with
  different sources.
- The spend side itself has more than one object for `CircleGroupOrder`.
- In privacy objects2, `R0P/CoreExt` was re-sourced and recompiled on
  2026-10-08 09:24, while its dependent `R0P/Copy` dates from 2026-10-07
  18:36 and was never rebuilt.

Consequence: every focused compile accepted so far, on both tracks, is
evidence that each module checks against the objects present. None is yet
evidence of one consistent theory. No accepted statement is withdrawn. But
**nothing is release evidence until one clean ordered build, from one source
per module name, on one base, with one axioms audit.** That is also the
outstanding "single Lean 4.32 kernel" item on the soundness side.

**D63.2 Lead decisions.**
- Adopt the design's target: a new workspace with one sources tree, one
  objects folder, Mathlib from AspisFormal, and the spend path's ported Aeneas.
  The build compiles in dependency order from a manifest with `--check`. Where
  the two sides' sources differ, take the spend copy and repair privacy
  imports.
- New item (f), the unified base, comes before (b), (d) and (e). The
  provisional soundness release roots are:
  - LiteralFreshAttemptBound, RawAdaptiveMembershipBound,
    AdaptiveMembershipSoundness;
  - SpendRelation, SpendAppendBinding;
  - the terminal/caller correspondence modules the live session lands.

  These are to be confirmed with the soundness side at final assembly.
- SemRows01 moves to (d), as a wire-decoder fact.
- On (e): the worker reads `line_identity` as the honest-data form of
  `match1`, not as an assumption of R1QueryResidualBridge. This is to be
  settled when the soundness side states which premise it would discharge.
- Attempt range for the integration build: 5000–5299, using the private
  joint launcher (same caps, slots and run2.py; only the objects folder and
  search path change). The build spans several night windows.

**D63.3 Done (on the side branch).**
- BatchedAlgebra and its dependents compile against the spend path's own
  `R1FoldCoefficientBridge`/`R1FirstFold` (byte-identical), with 0 coherence
  conflicts over 266 modules. So `line_identity` is stated over spend
  constants.
- `qm31SamplerLaw_spend` is proved on the spend base from the extracted
  `qm31_sample`, with the carrier transports, and `SamplerLawBridge.toSem1`
  is proved. They sit on different bases until (f).

### Lead acceptance of the own-column builder (2026-10-19); D64

The worker commits 0a3d14c9e..a1c258b5e are cherry-picked. The consistent
chain is 4481–4499 and 4510–4512 (`builders[2].consistent_chain` in
c3-evidence.json); the lead verified the new modules. Attempt 4501 hit -M7000
at 7.17 GB, and the worker split the module rather than raising the cap.

**D64.1 Proved.** `fill_own` has an extracted Rust copy, and its
differential test equals z9c on all five configurations:
- the QPrime own matrix: 2,952 sources, 1.11M entries;
- the G own matrix: 1,980 sources, 744k entries.

On the Lean side: `obs_lane`, `own_c1_ident`/`own_h1_ident`,
`own_src_ident` (the blockM/flatO layout), and `check_sound‴`, which removes
hOwn and hGOwn. The QPrime sources are now defined from the Rust descriptors
(`srcOf`), not assumed. The new premises are the builder runs and the
descriptor, width, layout and stride facts.

**D64.2 Remaining in check_sound‴.**
- hRel: needs a WideExact (8-limb) tower premise, the relR1 relations, and
  copies of design_relations/limb_functionals. It is a multi-session job.
- hRound, hGRound and hGBat.
- The decoder facts.
- The named input premises.

Memory: CertCheckSound4 peaks at 7.19 GB. Further composition must happen
at the CertData level, with no Aeneas import in the composing module.

All of this is subject to D63: release evidence requires the unified build.

### Unified-base build of the privacy closure (2026-10-19); D65: the R1 privacy theorems check in one coherent build

Side branch `codex/r1-privacy-build-integration-20261019` (dbfe84f12, pushed)
holds manifest 1: the closure of the privacy roots, 402 modules (8 spend, 237
base, 157 privacy). It was built from one repo revision (v8-reference
66bca8914 plus spend f05b0e63e) in the new host workspace
`aspis-joint-20261019`: one sources tree, one objects folder, AspisFormal
Mathlib and the Aeneas 4.32 port. The build ran in dependency order, one
module at a time, as attempts 5000–5402 (03:38–04:02 London), with 0 swaps
and peak 7.18 GB.

Where repo sources differed, the spend copy was used:
- the six narrowed base files;
- `V6PublishedTheoremInterfaces`, `R0P.LogUpChain`, `R0P.LogUpAssembly` and
  `R0P.SemRounds`.

**Lead verification.** All 403 host logs were parsed, including wrapped axiom
lists. The only axiom sets are subsets of {propext, Classical.choice,
Quot.sound}: 2,437 + 340 + 90 + 6 reports. The single `sorryAx` is in the
failed attempt 5068, which the error produced. The only non-zero exit is
5068: `AspisV8R19.R443BoundedRejectionMass` used `field_simp` without
importing it, and the old base supplied it through all of Mathlib. The fix
adds `import Mathlib.Tactic.FieldSimp`, an import-only change to the base
tree `v8-full-view-zk-20260912`. The lead accepts it; it must also reach
v8-reference's copy. It recompiled green at 5069.

The root theorems check with standard axioms only, in one coherent theory:
- `builder_witness_merged` (5283);
- `check_sound″` (5387);
- `privacy_R1_games` (5398);
- `privacy_R1_games_sampler` (5401);
- `privacy_R1_games′` (5402).

Object hashes are in `t2b2b/build-integration/joint-objects-manifest1.sha256`.
This settles D63 for the privacy closure. The soundness roots remain.

**Open (D63.2).**
- The soundness roots wait on soundness-side hygiene: three missing sources,
  the X/R1X double imports of SpendRelation/SpendAppendBinding/TraceAppend,
  and three name collisions.
- (c) end to end: the spend sampler stack in this workspace.
- (b), (d) (Rspend⁺ map, SemRows01) and (e).

### Lead acceptance at the 2026-10-19 cleanup: hRel at CertData level (D66), manifest 2 (D67)

**D66 (checker, hRel).** Worker commits 37b76b85c..82314d764 are
cherry-picked. The lead verified attempts 4513, 4601, 4602, 4607, 4609,
4610, 4613, 4614 and 4617: SHAs match, exit 0, standard axioms, no
overrides.
- `fill_rel` (WideExact ops, batched weights, both dual folds, line folds,
  relation coefficients) has an extracted copy; its differential test equals
  z9c's relation matrix exactly on all five configurations (499,328 and
  232,320 entries).
- The WideExact model (`CertRelW`): under `Tower B` and the new premise
  w·w = B.u, the extracted `wmul` is the product in K.
- `coefM_eq`, the weight/fold identities with weightsR1, w1, w2,
  lineFoldValue and naturalLineValue, and `rel_data`.
- `p_r1_of_data_rel`: `p_r1_of_data` with hRel discharged, at the CertData
  level (6.81 GB).

Not accepted: the pb/ct-level `check_sound⁗` wrapper. Two attempts (4615,
4616) hit -M7000 while loading imports, because any importer of Sound4
starts at about 7.18 GB. A larger-cap run is declined. The wrapper waits for
an import refactor of Sound2–4, with replays. New named premises: w·w = B.u
and the limb basis; the inverse transport ti = π⁻¹; the opening limbs; the
folded-position map fp (injective); query bounds; li = lineInverse and
x16 = storedLine16X on the line relations; size equalities.

**D67 (integration, manifest 2).** Worker head 167a70d73 is merged. The
lead verified attempts 5517 and 5520.
- `AspisR1Qm31ArithmeticProbe.{Funs,Types}` were promoted bytes-unchanged
  (Funs `114552b8…`, Types `c5a08408…`, matching the host extraction source
  and the accepted sampler journal). Their generated `maxHeartbeats`/
  `maxRecDepth` options are kept as generated.
- `privacy_R1_games_spendSampler` (5517, 4.12 GB): the QM31SamplerLaw
  premise is discharged from the extracted sampler, in one closure.
- T1 `toModel_toRust`, T2 `witnessOk_toRust`, T3 `pubCorr_toRustPub` (5520).
  T4 waits for the X/R1X decision.
- To fit under the cap, `R0Z.GoodDensity` and `R0Z.StatisticalDistance`
  were narrowed from `import Mathlib` to bounded sets (imports only). The
  dependents were rebuilt. `R1Z.EventsR1P2` then failed at `card_NZ` with
  kernel memory exhaustion: the narrower imports change the `Fintype`
  instance found for Fin 32 → UInt8. An import-only probe did not help.
  The unified build is stopped there: 425 of 455 modules current, with
  `privacy_R1_games′` and `check_sound″` not current on that base.
  Their standard-axiom status from manifest 1 (D65) stands for the
  whole-Mathlib base.

Deferred decisions, recorded as open:
1. EventsR1P2: a proof-level fix of `card_NZ` (count through `card_ans`),
   or revert the narrowing and size the composition another way.
2. The module of record for `AspisR1PublicPreparation.{Funs,Types}`, which
   has 3 and 5 repo copies; `SemRowsSpend` (`decSpend`, `semRows01_spend`,
   premise `RSqueezeAnswer`) is written and waits on it.

All agents are paused. No host job is running.

### User decisions (2026-10-19 evening); D68

1. **G_R1.1:** the ≤1.3M-per-transaction target stands and is to be met by
   arithmetic savings (~120k CU on the worst case), not by rebalancing.
   Recorded in `docs/research/100bit-spend-path-20261013/design/LEAD-DECISION-G-R1-1-20261019.md`.
2. **D54.3 resolved:** the production prover's writers (value, occupancy,
   path aux, bank merge, block, node, sponge, Poseidon) are to be replaced by
   the extracted copies in `refine/`, so `builder_witness_merged` is about the
   shipped prover. Prover-side only; no on-chain change. The migration goes
   through the standing gates (codec 1,233 outputs byte-identical, the
   ordered trace, checkpoint23, the saved fixtures, the 512-witness glue
   differential) and re-pins the extracted declarations.
3. **Lead rulings on the unified build (D67 deferred items):**
   - `EventsR1P2`: proof-level fix of `card_NZ`, counting through the
     existing `card_ans` equivalence; the import narrowing stays.
   - `AspisR1PublicPreparation.{Funs,Types}`: the module of record is the
     c16 copy the accepted proofs were compiled against (Funs `e98bb123…`),
     promoted bytes-unchanged like the Qm31 probe modules.

All work lands on `research`.


<!-- Original LOG.md lines 8090–8120 -->
## D145 (lead, 2026-10-22 03:45): part 32 merged; correction to D144 on BTreeMap

Merged `codex/cx-prover-commit32-20261022` (report
`r1p-final/PROVER-COMMIT32-20261022.md`; relaunched once after a Codex
capacity error, with a WIP snapshot commit kept). Proved in Lean, for the recursive sorted-list
publication reference: lookup totality, insertion/replacement, query-order
publication, sortedness, uniqueness and byte comparison. Standard axioms; all
three frozen ELFs rebuilt byte-identical (cfg-gated `sim_owned32.rs`).
Obstruction: the Kani check of the shipped BTreeMap transitions times out
(600 s), even isolated.

**Correction (lead error in D144).** D144 asked for Kani checks "against the
shipped BTreeMap". That contradicts D133: BTreeMap internals are not verified;
`std::collections::BTreeMap` is a named trusted item (`ProverCommitTrustedStd24.TrustedStd`:
`btree_empty`, `btree_insert_state`, `btree_insert_previous`, `btree_get`,
`btree_iter_ordered`, specifying it by the universal `Std.TreeMap` model). The
timeout is the predictable cost of that mistake. Corrected route: verify the
shipped *loop logic* with Kani with BTreeMap stubbed by an implementation of
exactly the TrustedStd contract (the sorted-list model), and connect the
native loop to the reference in Lean via the TrustedStd fields. If the shipped
code uses `entry(..).or_insert_with`, add it to TrustedStd as one more named
field with its documented semantics (get, then insert if absent), recorded
visibly on the trust list. Do not add any other field.

## D146 (lead, 2026-10-22 04:10): part 33 merged; correction to D143 ruling 1; statement-domain ruling

Merged `codex/cx-prover-commit33-20261022` (report
`r1p-final/PROVER-COMMIT33-20261022.md`). Per D145: exactly one TrustedStd
field added, `btree_entry_or_insert_with` (hit: map unchanged, callback not
invoked; miss: callback invoked once, value inserted and returned), a named Prop
hypothesis, not an axiom. Proved: folded-loop, ordered-consumer, query-answer,

<!-- Original LOG.md lines 8152–8255 -->
zero exhaustion ≤ 3/2^256 on a uniform raw carrier. J9095 standard axioms;
no shipped change, TrustedStd unchanged.
Stop: source control gives no OS-error bound below 1 (proved), so OS and
filesystem failures cannot be charged as a small δ.

**Lead ruling: OS and filesystem are an adversarial environment, not a
probability term.** Do not add a δ for OS/fs failure and do not assume an
error-free OS. Instead:
1. Model `getrandom::fill` outcomes, reservation create/write/fsync results
   and duplicate-nonce errors as an **environment schedule chosen by the
   adversary**, as a function of the call sequence (call index, call kind,
   prior outcomes). The schedule must not see the secret bytes being
   written: the OS is not assumed to leak file or RNG contents to the
   adversary.
2. Prove fail-closed behaviour on every failure path (`state_only_entropy.rs`
   172–196 and 919–962, `prover.rs` 354–375): nothing witness-dependent is
   published. Only a witness-independent error outcome is observable, and
   the simulator can reproduce it from the same schedule.
3. One named environment trust item, **E1 (OS RNG):** when `getrandom::fill`
   returns Ok, its bytes are uniform and independent of everything else.
   Record it on the trust list next to TrustedStd and P7, visible in the headline.
   The existing zero-exhaustion term 3/2^256 stays in the bound.
This makes privacy hold for every failure schedule, which is stronger than
any probability bound on failures.

## D148 (lead, 2026-10-22 05:20): part 35 merged; D147 refined: private ledger plus byte-blind faults

Merged `codex/cx-prover-commit35-20261022` (report
`r1p-final/PROVER-COMMIT35-20261022.md`). Proved: the byte-blind environment
schedule, `fail_closed` and `failure_replay` (on any failure the real and
witness-free simulator prefixes have identical observables, pointwise for
every schedule, with no OS/fs probability charge), reservation retention, the
extracted reservation bridge, and the E1-conditional zero-candidate bound.
Native control checks pass; J9127, 16 theorems, standard axioms; no shipped
change.
Finding: D147's schedule (seeing only index, kind and prior statuses) cannot
reproduce native `create_new`, whose occupied/fresh outcome depends on
whether the reservation path is already in the ledger (Lean proof plus a
real-filesystem probe). That is a lead modelling error in D147, not a privacy
problem.

**Refinement of D147.** The filesystem has real state. Model the reservation
ledger as **private environment state** with faithful `create_new`
semantics: it preserves existing entries and returns AlreadyExists iff the
path is present. The byte-blind adversarial schedule injects faults
(getrandom, create/write/fsync failures) around it. The adversary may choose
the initial ledger and add entries, byte-blind: chosen without seeing
any secret seed or path. A fresh path colliding with an adversary-chosen
entry is a bad event, bounded from E1 by (number of entries × attempts)/|path
space|, stated numerically. Add one named environment item, **E2
(filesystem):** `create_new` is atomic create-if-absent (O_EXCL), and
written/fsynced data persists. It sits on the trust list beside E1, TrustedStd
and P7. The reservation path is not made public.

## D149 (lead, 2026-10-22 05:30): part 36 merged; reservation address law comes from P1

Merged `codex/cx-prover-commit36-20261022` (report
`r1p-final/PROVER-COMMIT36-20261022.md`). Proved on the D148 model: private
ledger membership with byte-blind faults, retention, duplicate handling,
`fail_closed`/`failure_replay`; the exact E1 push-forward; the entry-count
union bound with the address-law hypothesis visible; a consistent E2 model.
J9134, 15 theorems, standard axioms; no shipped change.
Finding: E1 and E2 do not by themselves imply that SHA-256-derived
reservation paths avoid adversary-chosen entries (`E1_E2_without_uniform_paths`;
for a generic hash, a constant address function gives mass 1). Correct: that
inference needs a property of the hash.

**Ruling.** The address law comes from **P1**, the random-oracle model for
SHA-256 that the whole privacy and soundness argument already uses. No new
assumption is added. Obligation: under P1, for adversary-chosen entries
and every prior context, a fresh reservation address lands on an entry with
probability ≤ (entries + queries that hit the same input)/2^256. The part
"the adversary queried the oracle on this nonce input" is covered by the
existing seed-guess event. **Check domain separation:** the reservation hash
input must be disjoint from the protocol's oracle inputs (tag or length
prefix). If it is, it is an independent ROM coordinate. If it isn't, prove
the overlap is harmless or report it as a source finding. Do not change shipped
code.

## D150 (lead, 2026-10-22 05:45): part 37 merged; a new explicit reservation-guess event

Merged `codex/cx-prover-commit37-20261022` (report
`r1p-final/PROVER-COMMIT37-20261022.md`). Proved under P1 the fresh-address
entry bound and the frame separation of the reservation input from the
simulator-seed frame; control proofs for all 0–15 rejected nonce prefixes.
J9151, 19 theorems, standard axioms; no shipped change.
Finding (`no_existing_event_containment`): an adversary oracle query on the
reservation input (a memo hit) is **not** contained in the existing
`ProverCommitSeedEvent19.seedGuess`, which tests only the prefix
`UNPROVED:R1:SIM:COIN || simulatorSeed`. So D149's statement that the seed-guess
event already covered this was wrong (lead error).

**Ruling.** Add one new, explicit bad event, `reservationGuess`: some
adversary oracle query (or adversary-chosen ledger entry) equals a
reservation input or path the prover generates. Bound it by the same counting as
`seedGuess`: with a byte-blind adversary and uniform nonzero 32-byte nonces
(E1), the mass is ≤ (Q + entries) · attempts / (2^256 − 1) per run. Add that
term, stated numerically, **visibly to the headline bound** (before/after
shown) rather than absorbing it. At protocol parameters it is far below the
existing terms, so the < 2^-100 conclusion should still hold; prove that
inequality, do not assert it.

## D151 (lead, 2026-10-22 05:55): part 38 merged; ledger collisions coupled exactly, memo hits under the existing query budget


<!-- Original LOG.md lines 8378–8400 -->
extraction leaves as an external template.

**Ruling (same policy as D133/D145).** `std::collections::BTreeSet` is a
standard collection; do not verify its internals. Add exactly one named
TrustedStd field for `BTreeSet::from_iter` followed by iteration: the
result iterates the input's distinct elements in ascending order, i.e. the
sorted, deduplicated list (`List.mergeSort` of `List.dedup`, or the
`Finset` sort). Record it visibly on the trust list. Then prove that the
parent traversal built on it is sorted and duplicate-free, and that it
preserves the subsequent coin order.

## D157 (lead, 2026-10-22 08:35): part 44 merged; standing rule for std collection methods

Merged `codex/cx-prover-commit44-20261022` (report
`r1p-final/PROVER-COMMIT44-20261022.md`). Added the D156 TrustedStd field for
`BTreeSet::from_iter`. Proved: sorted, duplicate-free parent traversal with
coin order and state preserved; the native parent transition (536 Kani checks)
composed through all 18 tree levels. 15 theorems, standard axioms; shipped
files unchanged.
Obstruction: `BTreeMap::len` (which controls the final `program_tree`
Merkle-error guard) is not among the TrustedStd fields and cannot be derived
from them (countermodel). The direct native `indices.sort(); indices.dedup()`
Kani diagnostic timed out at 600 s and was not rerun.

<!-- Original LOG.md lines 8436–8467 -->
## D159 (user decision, 2026-10-22 10:20): side channels are in the privacy contract

The user ruled ("cover them") that timing and other side channels are **inside**
the privacy contract. This reverses the scope line in D143 rulings 2 and 3, which had put
them out of scope. It raises the target and does not lower it. Attempt counts,
retry counts and timings are now treated as potentially observable.

Leakage model, in three levels, each stated separately and never merged:
- **L1 (outcome counts):** the adversary sees the number of attempts/retries,
  which call failed, error codes, reservation/ledger effects and the number,
  order and sizes of everything the prover sends or writes. Proof obligation: the joint
  law of these is simulatable without the witness (witness-independent, or a
  function of public data and the simulator's own coins).
- **L2 (source-level trace):** the sequence of branches taken, memory/array
  indices, collection operations with key-dependent cost (e.g. BTreeMap
  insertion paths), allocation sizes, loop trip counts and variable-latency
  operations (division, inversion, early exits) must be witness-independent.
  Formal route: relational (2-run) properties over the extracted/owned code
  and Kani self-composition per function.
- **L3 (compiled code and hardware):** compiler and CPU constant-time
  behaviour **cannot be fully proved here**. It is either a named trust item
  (the compiler preserves L2 constant-time; the CPU's used instructions have
  data-independent latency), or measured (dudect-style tests, labelled as
  measurement, never as proof).
A witness-dependent retry or rejection-sampling count (for example a P_R1
predicate whose acceptance depends on the witness) would be a protocol-level
leak, and its fix (constant-work attempts or a witness-independent
acceptance law) would be a change to the frozen prover. Any such
finding is escalated to the user with a recommendation and is not patched silently.
First step: a side-channel inventory of the deployed prover path
(`r1p-final/SIDE-CHANNEL-AUDIT-20261022.md`), running alongside privacy
part 46.

<!-- Original LOG.md lines 8523–8573 -->
## D162 (user decisions, 2026-10-22 11:05): route, constant-time prover, L3 platform

The user decided the three D161 questions, each as the lead recommended:
1. **Deployment route = proof-account route** (public nonce = proof-account key,
   `generate_for_mask_nonce` → `prove_masked_retrying_with`), per the documented
   design (D38.4). The client/caller will be changed to call it, with new source
   pins and integration receipts. That is a host/client change; no verifier
   change. The devnet runner's 96-byte route is not the target.
2. **Constant-time host prover (L2).** Add constant-time field kernels and
   fixed-shape loops on the prover side only, and gate off TLS instrumentation
   in production builds. Constraints: the verifier ELFs stay byte-identical
   (dfc2a91a…, fb2fc048…, 121f3e29…); proof bytes are unchanged; each kernel
   gets a Kani/Lean equivalence proof to the current arithmetic and a two-run
   branch/index-trace check. It is an adoption candidate on its own branch,
   note-before-code, and is not frozen until its gates pass. Prior prover source
   pins are re-checked against it.
3. **L3 platform = x86_64 Linux native.** Pin the binary, compiler and flags, and
   a CPU model. L3 evidence is a disassembly audit plus dudect-style
   measurements, labelled as measurement, with compiler/CPU constant-time named
   as trust items.

## D163 (lead, 2026-10-22 11:50): L1 model layer merged; CT-kernel candidate passes against the new ELF pins

Merged `codex/cx-l1-coupling-20261022` (report
`r1p-final/SIDE-CHANNEL-L1-20261022.md`), proof-only. Proved: an ordered L1
attempt record with retry-control erasure; the conditional retry hazards and
iteration-entry laws for all eight attempts; capped two-seed entropy symmetry
and the ideal draw-count law; generic joint-TV union tools, with a numerical
candidate below 2^-100 that is **not** yet an established native bound.
J9880 standard axioms; no shipped change. No TLS leak or valid-spend
counterexample was found. Open: native event-producer refinement; the
joint mask/count/TLS/oracle coupling; equal-circle and query-abort integration;
composition with part 47.
Constant-time kernel candidate (`codex/cx-ct-kernels-20261022`, kept unmerged
as a candidate per D162; report `design/CT-KERNELS-20261022.md`): the design
note came first; branch-free M31/CM31/QM31/WideExact kernels behind a host-only
feature; TLS instrumentation gated off in production; 69 Kani harnesses
(equivalence plus two-run trace) and 41 native tests pass; transfer and withdrawal fixture
proofs are byte-identical. Its builds give default `40dc7574…`, devnet
`12cb0bc2…`, Pool `121f3e29…`. Those are exactly the current pins after the
user-approved S4 adoption (C3-BIN addendum 11:50), so the ELF gate **passes**:
verifier bytes are unchanged by the candidate. Single-run fixture measurements:
transfer 41.74 → 39.01 s, withdrawal 38.94 → 42.23 s (measurement only).
Remaining L2 items: sampler, sparse evaluation, query scan, multiproof
sharing, checker.

## D164 (lead, 2026-10-22 12:25): part 47 merged; y1 image proved for the owned reference

Merged `codex/cx-prover-commit47-20261022` (report
`r1p-final/PROVER-COMMIT47-20261022.md`). Proved: release field normalisation
and canonical embedded arithmetic; the recursive basis/evaluator with subfield

<!-- Original LOG.md lines 8609–8670 -->
## D166 (user decision and lead, 2026-10-22 18:20): L2 by simulatable trace; part 48 merged

**User decision (answering D165):** L2 for challenge- and private-coin-dependent
steps is met by proving the source trace **simulatable**: its joint law in the
real run equals the simulator's, up to the existing bad events. It is not met
by constant-time rewrites. Constant-time kernels stay only where secrets are
operands: the field arithmetic on witness-bearing values (F2) and the pole-check
arithmetic (F1). Consequence for the candidate: keep stage 2 (field kernels and
TLS gating), and drop the stage 3(a)–(e) fixed-shape rewrites from the
adoption candidate (they stay on the branch history as measured evidence). This
should restore prover time near the ~40 s baseline. The simulatable-trace
obligations for F3, F5 and F6 join the L1 coupling as proof work.
Part 48 merged (`codex/cx-prover-commit48-20261022`, report
`r1p-final/PROVER-COMMIT48-20261022.md`): native iteration bindings by
per-iteration Kani with owned-loop induction (the D164 route); interpolation
equal to `Lagrange.interpolate` with its 896-byte image; primal and dual folds;
gamma/kappa powers; seven-coefficient round accumulation. J9999 standard
axioms; shipped files unchanged. Stopped on an exhausted env J range. Open:
semantic samples and guards, final shift, weight-model correspondence, caller
composition.

## D167 (lead, 2026-10-22 18:50): constant-time candidate v2 per D166

Branch `codex/cx-ct-kernels-v2-20261022` (head `2b7a80b65a`, an unmerged adoption
candidate; v2 section in `design/CT-KERNELS-20261022.md`). It holds only the stage-2
field kernels and TLS gating plus a constant-trace pole check (`ct_pole.rs`):
branch-free QM31 equality and an eager scan over every slot, with no early exit.
Six compositional Kani gates, instrumented two-run checks and a full-size native
trace replay pass, and so do the fixture pole regressions. The verifier ELFs match
the adopted pins, and the fixture proof/public bytes are identical. Single-run
prover wall time (measurement only): transfer 38.51 s, withdrawal 37.95 s,
back at the ~40 s baseline. The stage-3 rewrites stay only on the old branch.
Remaining for L2: the simulatable-trace proof for the F3/F5/F6 steps (listed by
file:line in the v2 section); then candidate adoption gates and the L3 receipt.

## D168 (user feedback, 2026-10-22 18:55): prover slowdowns need a stop gate

The user called the stage-3 constant-time slowdown (about 40 s to 170–200 s)
unacceptable. It was never adopted: the v2 candidate (D167) is at the ~40 s
baseline. The process failure was the lead's. The stage-3 prompt had no
performance stop condition, so five successive slowdowns ran to completion
before review. From now on, every job that changes prover or host code carries a wall-time
budget gate: measure after each step and stop and escalate if any fixture's prover time
rises more than 10% over baseline. The stage-3 branch is evidence only and is
not a candidate.

## D169 (user, 2026-10-22 19:00): stage-3 branch removed; prover target under 15 s

On the user's instruction ("remove that shit if needed"), the stage-3
fixed-shape branch `codex/cx-ct-kernels-20261022` was deleted. It was never in
research. Its measurements are kept in D165; the v2 candidate is unaffected.
**New user target: prover wall time under 15 s per proof** (about 38–42 s today,
single-run on the x86_64 Linux build host). This is a performance requirement
alongside the security contract, not a replacement for it. Next: a profiling
job, with per-phase time, retry count and thread use, and a ranked list of
speedups classified by whether proof bytes and the existing proofs/trust
items survive. Notes: parallelism would touch the single-thread TLS trust item
and the side-channel model; any change to proof bytes touches the verifier
and soundness model and needs the user's approval.

## D170 (lead, 2026-10-22 19:20): prover profile; P_R1 is 89% of prover time


<!-- Original LOG.md lines 8938–9017 -->
## D185 (lead, 2026-10-23 09:15): privacy comparison contract is the mathematical simulator

The restatement job (`r1p-final/PRIVACY-RESTATE-20261023.md`) correctly stopped. The
existing deployed conclusion compares rust.real with `rust.ideal`, the ideal game run by a
Rust implementation. The proposed one compares rust.real with `source.ideal(simE)`. As
fixed-experiment propositions they differ, so this is a contract choice, not a proof step.
**Lead ruling (logged for the user, reversible).** The privacy contract is the standard
simulation definition: for every adversary, the deployed real experiment is within ε of the
ideal game run with the efficient mathematical simulator `simE`, whose cost bound is proved
for `simE` itself (the SIM-COST passes). The old conclusion together with conjunct 2 implies the
new one; the old is stronger only in additionally certifying a Rust implementation of the
simulator, which is never deployed and says nothing more about deployed outputs. The
previous theorem is kept unchanged; the new endpoint is added beside it with before/after statements.
Privacy work proceeds on conjunct 1 (the real side) using the worker's obligation map.

## D186 (lead, 2026-10-23 09:25): real-side privacy endpoint proved; real-prover refinement plan

Merged `codex/cx-priv-restate-20261023`. `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`
is proved from conjunct 1 alone. It compares deployed `rust.real` with `source.ideal(simE)`,
with the same error envelope (J10800, standard axioms). The old theorems are unchanged.
Lead assessment from the obligation map (`PRIVACY-RESTATE-20261023.md`): most of parts 27–55 bound
simulator code or proved shared helpers. The native refinement of the **real** prover
(`generate_for_mask_nonce` → `prove_masked_retrying_with` → prover.rs: masks, semantic
build, commitments/Merkle, transcript/sumcheck, opening, publication) is largely
unstarted as a whole, though many helper results transfer. Plan: three parallel
depth-first streams, each budgeted and using the routes that work (D144 owned references,
per-iteration Kani shipped = owned, Lean induction; never Aeneas on shipped iterator code):
R1 the retry/entropy/reservation owner on the selected caller (composing parts 34–43); R2 the
real commitment path (mask material, semantic build, commitments, Merkle, encoding); R3 the
real transcript, sumcheck, opening and publication. All target the research prover. The v2
candidate's differences transfer through its proved equivalence gates when it is adopted.

## D187 (user decision, 2026-10-23 11:05): proof-friendly prover rewrite

Real-prover refinement streams R1–R3 (merged): a host proof-account caller on the 64-byte
route with a durable ledger, where duplicate nonces fail closed and the verifier ELFs are unchanged; native/owned
control binding and an outer-owner bridge; mask-seed guards and context framing; transcript
rows 0–14 by reused part-30 callee contracts. Each stream stalled on Kani timeouts over shipped
prover loops (R2 at the scalar sampler contract, R3 at row 15), the same pattern S2 had before
the adapter rewrite. R1's +27% caller timing is from a contended shared host and will be
re-measured on a quiet host. **User decision:** rewrite the prover's control and per-attempt
pipeline (retry owner, mask material, semantic build, transcript, commitments, publication)
into owned, Aeneas-extractable code, with heavy arithmetic as small verified leaf kernels.
Base it on the v2 constant-time candidate, which is the intended host prover. Gates: design
note first; byte-identical proofs on fixtures for identical coins; at least 1,000 differential runs;
median prover time under 15 s on the build host (D168/D169); the verifier untouched. Host-only.

## D188 (lead, 2026-10-23 16:40): what "native" means for extracted code (S2 closure ruling)

S2-W keeps listing a residual "native-to-owned association" for code that Aeneas has
already extracted. Lead ruling: the project's source semantics are the Charon/Aeneas
extractions, as for every soundness cone (S1–S10, checkpoint, multiproof). Correspondence
between Rust source and its extraction is the existing extraction trust boundary (named
`AeneasExtraction`, beside rustc/P7). Correspondence between source and the deployed binary
is S10's ELF certificates plus P7. So for the extracted owned adapter, "native = extracted"
is not a new S2 obligation, and no per-call re-proof is needed. What S2 must still prove:
(i) the non-extracted wrappers, by their Kani contracts, which pass; (ii) composition of
the traced outer execution. Child-internal site events (verifier stage internals, the nine
internal sites) belong to the child cones and are carried as the named per-child cone-join
hypotheses. Multiproof's separate P6 total-oracle premise stays with the multiproof cone. With
this, the consolidated `S2CallerFacts` theorem should be statable. `AeneasExtraction` is added
to the headline trust list explicitly; it has always been implicit in every cone.

## D189 (lead, 2026-10-23 17:35): S2: the native AccountInfo ↔ heap association is the trust item's job

S2-W composed every field at the interpreted heap boundary: `callOrder`/`reachedPrefix`
by flatMap over the outer log; returned vector → write → checkpoint version; full account
frame and metadata. It stops at identifying native `AccountInfo` wrapper pre/post states
with the interpreted heap. Lead ruling: that identification is exactly what
`S2TrustedSdkBorrow` supplies. Its fields `account_data_cell`, `cell_payload`, `cell_counter`
and `borrow_frame` *are* the explicit trusted relation between the actual typed Rust carrier
and the abstract heap (plan, route B; C3-BIN 01:20), and the wrapper Kani contracts check the
native wrapper code against it. Vec snapshot allocation and cleanup are TrustedStd plus the
runtime allocator premise (allocation failure aborts the transaction). Child frames are empty on account
state because the owned design passes children only owned values and never an
`AccountInfo`. This is to be proved from the extracted signatures, not assumed. With these, the full
`S2CallerFacts` theorem follows. No new assumption is introduced. These are the existing items,
used for their stated purpose.



<!-- Original LOG.md lines 9018–9110 -->
## D190 (lead, 2026-10-24 10:55): entropy interpretation obstruction retained

The unmerged prover candidate at `7db89a0216` proves
`ProverRwEntropyIteration.no_retry_then_success`: a fixed pure external
getrandom.fill dictionary cannot produce a retry followed by success on the
same freshly zeroed buffer. Native E1 admits a zero draw followed by a nonzero
draw. The lead inspected that theorem and `no_two_draw_dictionary`; this is a
real obstruction to the proposed fixed-tape refinement, not a privacy attack.
Do not hide the false equality inside PrefixContract or BodyContract.

Authorize a proof/tooling-only effect-aware entropy interpretation carrying
an explicit tape cursor/world state through the actual entropy and retry owner.
Preserve every draw, errors, exhaustion, the unchanged bad-event probability
law, and joint L1/L2 observations. A hand-written stateful model alone is not
source refinement: connect it to the pinned source/emission with a checked
transformation or a proved sufficient observational transport. No new extraction
trust, RNG assumption, source change or security-contract change is authorized.
If existing tools cannot support this without new trust, report the smallest
concrete decision and its consequences. The zero-then-nonzero counterexample
remains a regression obligation.

The candidate's sampler/retry/salt helper results remain conditional on its
uninstalled external dictionary (260 function entries and 28 type carriers).
Audit 11261 passed in worker evidence: exit 0, 1.69 s, peak 4,266,180 KiB RSS,
swap 0, source revision d735d8174e plus exact source hashes, standard axioms.
This evidence is reused, not independently replayed; no candidate adoption or
release proof is claimed. Stage-3 budget used 60/100 Lean and 42/60 Kani;
continuation has 40 Lean and 18 Kani remaining, IDs beginning 11262 through
11399 subject to collision checks. Absolute quiet-host timing remains open.
See candidate `design/PROVER-RW-20261024-STAGE3-CONTINUATION.md`.


## D191 (lead, 2026-10-24 11:29 UK): effect packet reviewed; explicit entropy plumbing preflight

Candidate `748e710252` retains the fixed-pure-dictionary obstruction and adds
checked factoring of the emitted entropy owner. `ProverRwEffectOwner.pure_owner_eq`
and `ProverRwEffectRetry.client_retry` connect only the PURE specialization to
the emitted owner/callback. `owner_zero_then_one` proves the separate world
interpreter's two-read regression. The lead inspected these complete statements:
there is no native worldOwner equality or E1/L1/L2 transport theorem. The pinned
backend inspection finds no implemented implicit-world extraction option.

Read-only final-source/receipt/axiom checks pass. Worker audit 11288: exit 0,
1.80 s, RSS 4,264,628 KiB, swap 0, source 45e27024aa and exact hashes, standard
axioms. No new shipped changes or derived files over 5 MB. This remains on the
unmerged adoption candidate. Existing evidence was reused; no proof replay,
new native identity, privacy closure or new trust item is accepted.

D187 already authorizes a proof-friendly host prover rewrite as a gated
candidate. Within that scope, authorize an explicit entropy-state/coin-provider
interface in the HOST candidate, after a committed design and extraction
preflight. Preserve actual OS draw order and count, nonce rejection, entropy
error mapping, zero-buffer/zeroization behaviour, cap16 and outer retry behaviour,
including errors. State must actually distinguish successive calls and be
threaded across the complete retry owner; a constant ghost token or a reset
cursor cannot stand in for fresh effects. The native OS leaf must remain tied
to the exact existing E1 boundary; do not assume a whole-owner equivalence,
introduce new freshness/trust, or rename a missing source proof as an assumption.
The fixed-tape coupling must use the same event sequence, not merely equal
successful outputs. If this cannot be justified under the existing boundary,
stop the dependent source change with a concrete minimal decision for review.

First align the candidate with the already-approved H5 source change from
research. Any host refactor remains UNADOPTED pending source/effect equivalence,
relevant differential and L1/L2 gates, all three current ELF identities, and
quiet-host <15 s plus <=10% slowdown. Never change frozen verifier bytes or
adopt a backend patch/new extraction trust. Preserve all historical source and
counterexample evidence. Stage-3 budget is 84/100 Lean and 42/60 Kani used;
this preflight gets only the remaining 16 Lean and 18 Kani, IDs starting11289
through11399 subject to used-ID checks. A broader follow-up needs lead review
of this concrete preflight, not an unannounced budget reset.


## D192 — explicit entropy preflight reviewed; cap16 source gate next (2026-10-24)

Candidate ece5baabbc remains unmerged. The source-derived owned Draw64
prototype is extracted with real changing provider state; concrete_zero_then_one
consumes two entries from one finite Tape and returns cursor2. Error and cap
control preserve provider state. Four final module hashes and nine standard
axiom reports were checked; audit11305 at ddb833a1cd exited0,wall2.14s,
RSS3873112KiB,swap0. Same-event runtime coverage is26214 LOCAL entropy-helper
cases, and Kani proves an arbitrary-input ONE-iteration source cut only.
Neither establishes universal cap16 or cap8/native event correspondence.
No crates/programs change against H5 base71100fccbd; no ELF/timing rerun.

E1/E2, native error-carrier association, physical cleanup, callback/retry and
joint L1/L2 transport remain undischarged. Generated Emission carries explicit
heartbeat/recursion defaults; the next stage must remove them in adaptation
and validate the affected closure under default options. No limit increase is
authorized. This is a proof-configuration cleanup, not a rejected mathematical
claim or permission to substitute a model theorem for native refinement.

Stage3 consumed100/100 Lean and44/60 Kani. After review, authorize a separate

<!-- Original LOG.md lines 9670–9700 -->
## D190 (lead, 2026-10-25 13:05): lead resumes; the Codex-manager period is wound down

From 2026-10-24 10:00 to 2026-10-25 12:30 a Codex manager ran the loop. In about 27 hours there were
about 500 commits, and about 114 of them concerned launcher, admission, metadata, monitor, installer,
staging and memory-policy machinery rather than proofs. Root cause found by the lead: the manager
rewrote the worker Lean rules (scratchpad `local-lean.txt`, 00:16) to `-M4400` with extra pinning,
I/O and deadline rules. Ordinary imports peak at about 4.2–4.4 GB, so compiles hit Lean's internal
4,400 MB ceiling, which was then treated as a host "memory failure". Each failure spawned more
infrastructure review. The build host itself is healthy (52 GB available, low load). Actions: the
lead's rules are restored (`-M7000` inside 6G/8G scopes; workers do not build or repair
infrastructure; on launcher trouble they stop and report). The manager's running job
`cx-port36-transport` was stopped, with a WIP snapshot kept. Proof results the manager merged are kept
(e.g. the concrete Claims parent and S1 finish connection, and Q1/Q2 port modules). Infrastructure
changes are left in place but no longer required by worker rules.

## D191 (lead, 2026-10-26): prover candidate status and its ELF divergence

The proof-friendly prover candidate (codex/cx-prover-rw-20261023, UNMERGED) now has query refinement, entropy/retry modelling (exhaustion 2^-4080 per call and 2^-4077 over eight attempts, as CONDITIONAL model results) and 74 of 262 operation-dictionary interpretations. Conjunct 1 of RustProverRefinement remains a premise. A second worker (codex/cx-prover-dict-20261026) covers the off-path entries. The default ELF built from the CANDIDATE branch's source hashes to d7d42f77..., not the release pin f8c0ec72.... Production is unaffected: lowering2 reproduced all three release pins from research. The candidate branched before the adapter/H5 adoptions and edits shared aspis-core files. Before any adoption it must be rebased onto research, and its effect on the verifier ELF measured; any verifier-byte change needs owner approval. Privacy target not yet established.

## D192 (lead, 2026-10-26): host barrier cap correction for the prover candidate

The prover-candidate host barrier (/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py) asserted exactly MemoryHigh=5G / MemoryMax=7G. That rejected every launch at the policy caps 6G/8G (run-joint.sh MX=8), which are required for Lean -M7000. Lead edit (one line; backup barrier.py.bak-lead-20261026): the assert accepts exactly the pairs {(5G,7G),(6G,8G)}, with swap 0 and pids 64. Nothing above policy is accepted, and the reservation scanner is unchanged. Separately, workers follow local-lean.txt rule 6: one scope at a time per job, and wait/retry at the aggregate reservation barrier.
