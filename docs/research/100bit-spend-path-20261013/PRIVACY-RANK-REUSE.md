# Privacy/rank reuse inventory — 2026-10-14

Read-only inventory for root. This records declared interfaces and evidence scope; it does not determine whether any premise applies to R1.

## Pins checked

Current worktree `codex/100bit-spend-path-20261013`, HEAD `e21211727fc6ad53a2ef014d3fa3dda72037cef0`.

| Source | SHA-256 |
|---|---|
| `docs/research/100bit-spend-path-20261013/PRIVACY-RANK-PATH.md` | `eed5efaaa65c7caf0a470fa6d230856de54f86849d50d7eea23897128d4604b4` |
| `docs/research/100bit-spend-path-20261013/DUAL-PAD-WORD-BRIDGE.md` | `02f1818d17e7df0058de361cd6c1117b8d1f454ff2334a6f297cbea01837b8b3` |
| `lean/DualPadWord.lean` | `62372ace48d87078cc459dd887b1b8e4f4897f307e2b37e837bda3849c3de58b` |
| `lean/DualPadLift.lean` | `5f7c11b7cf8c66ce8a5de7b888eaa99de1e61b32d160f4c44dec775c717676ca` |
| Old `v8-r0-zk-20261009/lean/R0Z/MaskLayout.lean` | `4f0615a66f8abe90b80d1cdff56961356cff13628c85dbd3456f43d9f425b43a` |
| Old `R0Z/Z4Maps.lean` | `5e92064e8f9f0f71a5da98a139f1dba8fa3b4463e40831e317f22246e0c63ceb` |
| Old `R0Z/Chain.lean` | `c0e5ce0ffd53bee97a8ac9a7c66be4b6d639aac296259416f7799ccaa3e0a4e8` |
| Old `R0Z/GoodDensity.lean` | `a4624e603bc89ad8761f6a2df6a50aecc45f7efa0c9d8abac535158beb90322f` |
| Old `R0Z/QuotientImage.lean` | `c380622230deaef7db8769351ccf8a44989c36b13895d71169f314fc49dc08c9` |
| Old `R0Z/D12.lean` | `272b92f8066f63cf4b57781cfa1f6e586377fadcb1682390acaebda7e4761162` |
| Old `R0Z/HonestView.lean` | `f331f2b7e0ffc7c755328d9c1b7d318990fcfca14d2bb63ba3f185611a8c7446` |
| P3 rank-gate README / receipt | `3a278883aa6ced010248ff8d030b2419492fe337c7e9c4997a2d1c1ba3b44589` / `9e050c3376ad89822aff79b9c2285c717756fab4877ead85369405273ae96c78` |

The `R0Z/Z4Maps.lean` definition is unchanged in the available z4a, z4b, z4c, z5, z6, z7, z8, and z8b branches. No later Lean theorem closing the declared rank/image targets appeared in these trees.

## Existing formal APIs and boundaries

- **Old mask layout and legal coordinates:** `R0Z.MaskLayout.eligible` is a relation on `Fin 29 × Fin 1024` requiring one of columns `0..15` and its eligible row predicate (`MaskLayout.lean:38-44`). `EligibleNoise K F := EligibleCell → F`, `AffTape K F := AffCoordinate → F`, and `MaskTape K F := MaskCoordinate → F` (`:50-61`). Thus eligible semantic noise is over the subfield `F` (the M31 role); each old extension lane is represented by four `F` tape coordinates and packed to `K` by `pack4` (`:72-76`), with extension lanes ordered G, H1-padding, D. Balancing and the H1 padding/copy-active restriction are literal in `balance`, `h1Padding`, and `applyAff` (`:81-99,107-116`). This is a different declared domain from arbitrary `K`-valued C1/repair words.
- **Raw observation and surjectivity targets:** `R0Z.Z4Maps.roundMaskMap`, `silentMasks`, `silentRoundMaskMap`, `c1Projection`, and `c1Map` are definitions (`Z4Maps.lean:19-47`). `roundMask_surjectivity` and `c1_surjectivity` are also only `def ... : Prop`, not proved theorems (`:52-65`); the file comment explicitly says they are unproved targets and no rank computation is made (`:4-6`). Their form is challenge-indexed (`ch : Challenges K`) with `Good ch`, honest witnesses/public equality, transport permutation and pack basis. `roundMask_surjectivity` asks for a silent-mask preimage of the particular `roundProjection (sRem ...)`; `c1_surjectivity` asks that a particular public-instance C1-projection difference lies in `range c1Map`. Neither states unrestricted onto-ness for an arbitrary raw observation vector.
- **Affine law:** `R0Z.D12.MaskImage` is an explicit conditional proposition comprising (i) per-round remainder in the mask-linear range and (ii) same-public instance offset in the common range (`D12.lean:74-78`). `payload_law` and `hvzk_perfect_of_maskImage` consume that proposition (`:101-123`); they do not prove it. `AffineLaw.equal_laws_of_mask_image` is the generic equal-coset law once range equality and displacement-in-range are supplied; no R1 rank or raw-map fact is inside it.
- **Normalized sumcheck remainder:** `R0Z.Chain.sRem_mem_chain0` is a proved membership theorem. Its assumptions include honest prover/build, pack basis, statement, witness, challenges, noise and `alpha ch 9 ≠ 1/2`; its conclusion is only `sRem ... ∈ Chain0 ch` (`Chain.lean:275-287`). `Chain0` is the intersection of the initial constraints, nine chain equations, and terminal evaluation kernel (`:137-164`). It does not prove `Chain0 ch ⊆ range (silentRoundMaskMap ...)`. The latter was explicitly the still-open T2b-2 image obligation in the old LOG. The old `roundMask_surjectivity` Prop is the nearer statement, but remains unproved.
- **Challenge exceptions:** `R0Z.Shift.GoodAlpha a := (∀j, a j ≠ 0 ∧ a j ≠ 1) ∧ a 9 ≠ 1/2` (`GoodDensity.lean:16`). `badAlpha_density` proves at most `21 / |K|` for a uniform vector in `K^10` (`:86-100`), via the 21 coordinate pins. The FS layer `badMass` stays generic; `zkfs_of_maskImageOn_good` takes an external bound on it (`FsGood.lean:29-31,119-129`). This does not include the R1 additional `gamma ∈ K` exception required by `DualPadQuadratic`/`DualPadLift` (`gamma.im ≠ 0`), nor does it provide a joint density result for the actual WideExact sampler/history.
- **Unrelated encoder quotient surjectivity:** `R0Z.HonestView.QuotientImage.endpointLinear_surjective` is a valid algebraic theorem for two distinct OOD endpoints; `quotient_mem_image_of_nonrational` then shows a specific quotient word is in `range exactInitialEncoder` given distinct, non-base-rational endpoints (`QuotientImage.lean:20-34,90-122`). Its domain is `InitialMessage K`, codomain K×K / encoder word `Fin 1048576 → K`; it is not the mask raw-observation surjectivity needed here.

## Finite rank evidence

`PRIVACY-RANK-PATH.md:92-105` and `evidence/privacy-wide/proof-rank-gate-p3/README.md:1-31` report one parsed, accepted P3 transfer proof with actual WideExact gamma/challenges/22 query positions and D18 transport: eligible C1 raw ranks 112 each (16 maps); balanced H1 raw rank 94 in ambient dimension 95; compensated pure-round image rank 1080; initial-zero part rank 1076. The log's exact rows are `transfer13.log:1081-1084`: `H1_BALANCED_RAW rank=94 ambient=95 inactive_rows=810 forced_inactive_sum_coordinate=1`, and `PURE_PROOF_RANK image_rank=1080 initial_zero_rank=1076 expected_image=1080 expected_silent=1076`. The README records this as one actual accepted P3 proof, not a theorem/density statement. Receipt uses `--release --locked --offline --features private-leaf-salts`, exit 0, 36.5363 s, 4G/6G/0 cap; see `transfer13.json`. Probe inputs are hash-pinned in `inputs-sources.json` (probe.rs SHA `54ec15ab6aa9205d3a07d4de56680cd301b6fdfb769dd6281d17b2fb7a13b531`, z5.rs SHA `b8c7e3198bae60b59ccaf3aa1e7877bf9f27489fade9473de4a76bfb0958796b`, plus manifest/lock and proof/public hashes). The source bundle itself is remote evidence, not Lean source.

The reported rank 94 is deliberately short of the 95-dimensional listed ambient space; it is not an onto certificate for that whole space. Rank 1080 is the compensated experiment's pure-round image, while 1076 is its initial-zero part. They are numerical results at that actual challenge/transcript, not a universal rank theorem. `SECURITY-PATH.md:139-142` explicitly distinguishes other WideExact R0 payload experiments from this R1 rank gate.

## Interface comparison with the current dual-pad lemmas

`DualPadWord.repair_mem`/`repair_raw_zero`/`full_word_eq` and `DualPadLift.correction`/`observations_eq` are generic symbolic identities. `DualPadWord` assumes one common `K`-linear submodule `B ⊆ (I → K)`, `K`-linear raw observation, and for every lane a pair `delta c, noise c ∈ B` with `raw(noise c)=raw(delta c)`; `DualPadLift` additionally assumes a rootless quadratic extension `E/K`, exponents 27/28, and `gamma.im ≠ 0`. None proves those preimages or a rank property.

The prior R0Z eligible-noise declaration is `F`-valued and only semantically eligible cells are sampled from it; old full tape is `F`-valued and embedded/packed into K. The dual-pad repair words are `K`-valued and use K-scalar linear combinations. The required extension of old F-linear raw ranks/ker/image statements to the exact K-linear `B` and raw map has no theorem found. Similarly, old `roundMask_surjectivity` is the still-open old-field normalized payload target; its old `Chain0`, dimensions, point layout and `Good` condition do not by themselves identify the R1 WideExact + D18 + two-pad model. The P3 rank experiment does exercise the actual WideExact two-pad formula for one instance, but does not certify those universal interfaces.

No existing formal proof found for arbitrary-point raw observation surjectivity; a universal 94/95 H1 image; pure-mask `Chain0` image inclusion for R1; or a good-challenge density theorem including `gamma ∈ K`. The generic linear correction API is reusable only after the exact subspace, field scalar action, raw map, and universal preimage premises are independently established.
