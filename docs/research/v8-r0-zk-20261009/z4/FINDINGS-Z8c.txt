Z8c -- silent rank on the BALANCED Lean mask space (T2b-2b design §3.3)
=====================================================================

Base 054164c8c (origin/v8-reference). Branch codex/z8c-balanced-20261015.
Exact M31/QM31/WideExact computation; not a Lean proof; no Lean or
production source changed. Lead converts this text to .md.

STOP: none. (S1), (S2), (S3_u) annihilate bat on ker own exactly (0
violations on 16,542 own-kernel carries per job, every job). The balanced
silent rank is 1,076 on A, J, K, M; it is below 1,076 only on B, I, L,
which are degenerate challenge structures (the deficits are in §3). Every
number below is identical on all 5 vectors of its structure: the per-job
outputs hash-identical after removing labels and timings, and K and M are
byte-identical to A.

0. Model
--------
* Sources follow R0Z/MaskLayout.lean exactly: maskOnlyColumns = balance 0
  (raw), lane 27 = balance 0 (pack4 raw G), dWord = balance 0 (pack4 raw D);
  `balance 0` puts minus the sum of the other copy-inactive rows at row 0.
  Per lane and per limb the sources are e_r (r active) and e_r - e_0
  (r inactive, r != 0): 1,023 per F-lane, 4,092 per K4 lane (G, D). The raw
  row-0 coordinate is overwritten and contributes nothing. Row 0 is
  copy-inactive (asserted).
* No .inactiveSum proxy. On these sources the batched .inactiveSum is
  identically 0; the probe checks it on every own-kernel carry and reports
  its pivot count.
* Everything else as Z8: Z4c vectors 0..4 replayed, WideExact opening
  challenges (same seeds), Lean totalWeights with the kappa^4 libraWeight
  term, column-wise prover::quotient, real linearPayload per-lane silence
  coordinates (3 point claims, extra claim, 2 OOD, 88 opened symbols per
  lane), elimination per lane on own coordinates then globally over
  [batched 2,112 | round 1,084].

Preflight record (structure A, vector 0, --preflight, no targets)
-----------------------------------------------------------------
preflight 1 (aspis-z8c-preflight): all items ran. Silent 1,076;
  (S1)/(S2)/(S3_u) annihilate exactly. Two design sub-predictions failed
  (D-high_bal 1,808 not 1,800; G-low 220 not 224), and the left-kernel
  remainder printout was unreadable (dense, unreduced).
  Code change before the full run: the remainder basis is fully reduced and
  printed as coordinate ranges; f-prefix projection ranks added; a G-low
  variant without G's extra claim added; the (B) assembly rank of D-high_bal
  plus G's (ker R_G ∩ ker own_G) batched image added. No change to any
  gate quantity.
preflight 2 (aspis-z8c-preflight2): same numbers plus the new diagnostics.
The full run uses the preflight-2 source.


1. Gate on the balanced model (item (1), (2), (4); all 5 vectors identical)
-------------------------------------------------------------------------
 struct Good3 Lambda_0..9           | silent | init.ret. | R(M_bal) | R(ker own) | bat ker own | bat ker own∩ker R | ia piv | chain0 exc | i'    | ii'   | full cond.
 -------------------------------------+--------+-----------+----------+------------+-------------+-------------------+--------+------------+-------+-------+-----------
 A  yes  1,2,4,4,4,4,4,4,4,4        | 1,076  | 1,080     | 1,084    | 1,080      | 1,912       | 1,912             | 0      | 0          | 25/25 | 25/25 | 1,080
 B  no   1,1,1,1,1,1,1,1,1,1        | 1,038  | 1,042     | 1,066    | 1,042      | 1,912       | 1,912             | 0      | 38         |  0/25 | 25/25 | 1,080
 I  no   1,2,2,2,2,2,2,2,2,2        | 1,068  | 1,072     | 1,080    | 1,072      | 1,912       | 1,912             | 0      | 8          |  0/25 | 25/25 | 1,080
 J  no   1,2,2,2,2,2,2,2,4,4        | 1,076  | 1,080     | 1,084    | 1,080      | 1,912       | 1,912             | 0      | 0          | 25/25 | 25/25 | 1,080
 K  no   1,2,4,4,4,4,4,4,4,4        | 1,076  | 1,080     | 1,084    | 1,080      | 1,912       | 1,912             | 0      | 0          | 25/25 | 25/25 | 1,080
 L  no   1,1,1,1,1,1,1,2,4,4        |   994  |   998     | 1,076    |   998      | 1,912       | 1,912             | 0      | 82         |  0/25 |  0/25 | 1,073
 M  yes  1,2,4,4,4,4,4,4,4,4        | 1,076  | 1,080     | 1,084    | 1,080      | 1,912       | 1,912             | 0      | 0          | 25/25 | 25/25 | 1,080
 bat ker own ∩ ker R = span rank of the [bat | round] carries minus dim R(ker own)
 (exact identity; e.g. A: 2,992 - 1,080). R(ker own) is with the initial sum
 retained; with the initial sum zero it is silent + 0 in every row (A: 1,076).
 The (Q') check (Chain0 basis against R(ker own) with initial 0) has excess 0
 for A, J, K, M.

 Per-round silent ranks (max 108 at rounds 0 and 9, 112 otherwise):
   A, J, K, M  108 112 112 112 112 112 112 112 112 108   per limb 28 (27 at rounds 0, 9)
   B           108 112 112 112 112 112 112  93 112 108   round 7 limbs 24, 26, 21, 22
   I           108 112 112 112 112 112 112 108 112 108   round 7 limbs 28 each (joint loss)
   L           108 112 112 112 112 112 112 108 112 108   round 7 limbs 28 each (joint loss;
               the per-round projections sum past 994, so the deficit is joint
               across rounds)

 Comparison with Z8 (unbalanced). For A, B, I and J, the silent rank,
 initial-retained rank, per-round and per-limb ranks, chain0 excess, and the
 i'/ii' pass counts and excess pivots are identical to Z8's. The batched
 pivots are 1,912 rather than Z8's 1,920 and the span rank is 2,992 rather
 than 3,000. Both differences are the 8 .inactiveSum limbs, which are now
 identically 0. On these vectors, then, F4's model gap costs nothing:
 1,076 is a measured rank of the Lean (balanced) model, not only an upper
 bound.

2. Verifier relations and the left kernel of bat on ker own (item (5), first part)
---------------------------------------------------------------------------------
 The 25 candidate relations (ia; S1 = check_v2 with Lean totalWeights and
 fold::dual_fold; S2 = h0 + h4; S3_u = exact_final_encoder(f, u) = 0 for
 the 22 queried fibres) all hold on every own-kernel carry. The
 annihilator of bat(ker own) inside the 2,112 batched limbs has dimension
 200, the 25 relations span it (F-rank 200 = 8 + 24·8), and nothing is
 left unexplained. F2 is confirmed on the balanced model, and the 24
 relations are independent.

3. Deficits (structures below 1,076; stop rule (A) is a finding, not an error)
-----------------------------------------------------------------------------
 B: deficit 38. The chain0 excess pivots are the 38 round-7 coordinates of
    Z8's list. The i' excess pivots are (7,14,2) (7,15,2) (7,16,2) (7,16,3)
    (7,17,2), identical to Z8.
 I: deficit 8, at (7,24..27,{2,3}). The i' excess pivots are (7,24,2)
    (7,24,3) (7,25,2) (7,25,3) (7,26,2), identical to Z8.
 L (alpha_0..5 in F, alpha_6..9 uniform; Good2' with i = 6 only): deficit 82.
    The chain0 excess is 82 (699 of 1,080 units fail). Its support is
    (7,7,{2,3}), (7,8..27,{0,1,2,3}) and (9,27,{0,1,2,3}). The i' and
    derivative diagnostics fail 5/5 per vector with excess 5 and pivots
    (7,7,2) (7,7,3) (7,8,0) (7,8,1) (7,8,2).
    (ii') also fails 5/5 per vector. The full conditioned image (semantic
    lanes and H1 added) is 1,073, not 1,080. The batched coordinates of the
    ii' targets are all matched (0 unmatched); the round residual has excess
    5 with pivots (7,26,1) (7,26,2) (7,26,3) (7,27,0) (7,27,1) and support
    (7,26,{1,2,3}), (7,27,{0,1,2,3}), (9,27,{0,1,2,3}).
    So under L the witness-difference targets fall outside even the full
    conditioned span. Good2' with i = 6 alone does not reach the target:
    this is a failure of the statement, not only of the proof route. It
    answers design §3.3 (8)(L) and the question left open in F6/A7.
 K (alpha_2, alpha_3 in F, so Good3 fails with exactly two of alpha_0..3
    outside K2): passes; Lambda_2..9 = 4. Good3 is sufficient, not necessary.
 M (Good3 holds minimally): passes, as required.

4. Per lane (item (3); balanced sources; ranks in limbs)
-------------------------------------------------------
 Structure A (identical for K and M):
 lane    own | rank R_l | R_l(ker own_l) | own on ker R_l (claim0 c1 c2 extra) | own on R_l^-1(V_!=l) / dim V_!=l | claim2 rank on ker R_l,6
 m0 e1   112 |   64 |  60 | 108 (0 4 4 4) | 108 / 1,080 | 4
 m1 e3   112 |  112 | 108 | 108 (0 4 4 4) | 108 / 1,080 | 4
 m2 e5   112 |  152 | 148 | 108 (0 4 4 4) | 108 / 1,080 | 4
 m3 e7   112 |  192 | 184 | 104 (0 4 0 4) | 108 / 1,080 | 4
 m4 e9   112 |  224 | 216 | 104 (0 4 0 4) | 108 / 1,080 | 4
 m5 e11  112 |  256 | 248 | 104 (0 4 0 4) | 108 / 1,080 | 4
 m6 e15  112 |  316 | 308 | 104 (0 4 0 4) | 108 / 1,080 | 0
 m7 e17  112 |  340 | 332 | 104 (0 4 0 4) | 108 / 1,080 | 0
 m8 e19  112 |  364 | 356 | 104 (0 4 0 4) | 108 / 1,080 | 0
 m9 e21  112 |  388 | 380 | 104 (0 4 0 4) | 108 / 1,080 | 0
 G       376 |  660 | 652 | 368 (0 4 0 4) | 372 /   904 | 0
 D       376 |  220 | 216 | 372 (4 4 4 0) | 372 /   992 | 4
 OOD (8) and opened (88; 352 for K4 lanes) are full on ker R_l in every lane
 and every structure.

 Deviation from §3.3 (3). The design expected 108 for e <= 13 and 104 for
 e >= 14. Measured: 108 only for e in {1, 3, 5}; 104 for every e >= 7. On
 the whole kernel of R_l, claim_2 is a function of the lane's rounds
 already for e = 7, 9, 11. The narrower F5 statement (claim_2 in
 rowspace(R_l,6), round 6 alone) holds exactly as predicted: e >= 15 and G
 yes; e <= 11 and D no. So Rel_l in OT_l must include claim_2 for
 e in {7, 9, 11} as well, with those lanes using rounds beyond 6.
 Expected G 368 and D 372: confirmed.
 OT' (§2.4.4): every mask lane loses only claim_0 (108). G and D lose
 nothing beyond one block (G 372 = all but claim_0; D 372 = all but
 extra).
 Other structures: J matches A except R ranks 40..238, m9's
 dim V_!=l = 1,072, and m5's F5 rank 3. B and I have F-/K2-valued claims
 (own 100/104). L has own on ker R_l = 104 for every mask lane,
 OT' 104 for e >= 3, and dim V_!=l of 984..992. The full per-lane lines are
 in probe-Z8c.log (Z8C_LANE_OWN / _OT / _OTPRIME / Z8C_F5).

5. D-high, the x^28 law, and Z8b's residual (item (5), second part)
-------------------------------------------------------------------
 D-high_bal = D words with c_k = 0 for k < 56 and sigma_D = 0 (sources e_r for
 active r, e_r - e_303 for inactive r; row 303 is the first inactive D-high
 row; row 0 has coefficient 89).
   own_D rank 372; rank bat on D-high_bal ∩ ker own_D = 1,808 (expected 1,800).
   Left kernel: dimension 304 inside the 2,112 limbs. ia, S1, S2 and the 22
   S3_u relations hold (200). All 14 low-fold coordinate functionals
   f0..f13 FAIL, each nonzero on 56-64 image rows. Unexplained: 104 limbs.
   Projection ranks of the image onto f[0..m): m = 1,2,4,8 → 8;
   m = 12,13,14 → 16; m = 15 → 24; m = 16 → 32; m = 20 → 64; m = 32 → 160;
   all 256 f → 1,776; h → 48.
   Modulo the explained relations, an echelon basis of the remainder (104
   rows) is supported on [h2..h6, f22..f255] (the S3 relations eliminate
   f0..f21).
 Z8b's (P) block rerun (unbalanced, every D row with coefficient >= 56):
   bat rank 1,812 (Z8b 1,812), with 4 ia pivots. S2 fails (h0 + h4 != 0 on
   4 rows) and S2u = h0 + h4 - quarter·ia holds. The other 23 verifier
   relations hold and the f0..f13 coordinates fail. Unexplained: 108
   = 104 + the 4-limb complement of D's K4-line in ia. The f-prefix
   projection ranks are identical to the balanced block.
 Reading. The design's x^28 law predicts that D-high misses the 14 low
   fibres f0..f13 as coordinates: 112 limbs, giving 1,800 (1,804
   unbalanced). Measured: D-high misses 104 limbs (13·8), and these are
   not the coordinates f0..f13. D-high reaches 16 limbs inside f0..f13 and
   is deficient further up (f[0..16) only 32). This accounts exactly for
   the 8-limb residual of §2.5.1 (1,812 = 2,112 - 8·(13+22+1+1) - 4). The
   residual is the low-block count, not the S1/S2 conventions. A hypothesis
   I have not checked: the probe's coefficients are NaturalBasis
   coefficients (encoder::eval_pair uses basis::values, not monomials), so
   "c_k = 0 for k < 56" is not "divisible by x^28", and §2.5.1 as stated
   does not apply to this basis.

6. G-low and the assembly of (B) (item (6))
------------------------------------------
 ker R_G ∩ ker own_G has dimension 3,064.
   Restriction to rows pi^-1(0..55): rank 220 (expected 224). Without G's
   extra claim among the own functionals: 224. The extra claim is
   libraWeight on coefficients k < 56, i.e. a functional on exactly these
   rows, so own-silence costs one K4 line there.
   Low-fold coordinates f0..f13 of G's batched image: 112 (expected 112);
   jointly with the rows, 236 (240 without extra).
   G's own batched image on ker R_G ∩ ker own_G: 1,904. Its f-prefix ranks
   are full (8·m for every m <= 128).
 Assembly: rank of bat(D-high_bal ∩ ker own_D) + bat(G ∩ ker R_G ∩ ker own_G)
   = 1,912 = bat(ker own). (B) is reached by the two absorbers D-high and G,
   on every structure. The split between them is not the f0..f13
   coordinate split of §2.5.3, and G-low must be stated modulo G's extra
   claim.

7. PR6 / PR7 (item (7); G words in one prefix block, unbalanced; all structures)
------------------------------------------------------------------------------
 PR6: fresh-at-6 G space (rounds 7..9 zero) has dimension 32 limbs, with
      round-6 leading degrees 27..20 (4 limbs each). Its deg <= 22 part has
      dimension 12, and claim_2 has rank 4 on it: PR6 holds.
 PR7: the round-7 span of G (one 3-bit suffix block) has dimension 32, with
      leading degrees 27..20. Its deg <= 22 part has dimension 12, and
      claim_0 has rank 4 on it: PR7 holds.
 These match P3's degree ranges (§2.3.4/§2.3.7).

8. Code
-------
z8c.rs is a module of probe.rs dispatched by `--z8c`. The probe.rs changes
are the `mod z8c` declaration and one dispatch line. The z8.rs body is
copied verbatim: trial replay, alpha helpers, round_polys, Proj, WideExact
opening challenges, Lean totalWeights, column-wise unit quotients, Ctx,
lane_stage, conditioned_sources (ii'), slice_image, batched_reduce,
decomposition_check. The only changes there are print tags (Z8_ -> Z8C_)
and STRUCTURES/alpha_for extended by K, L, M, appended so that A, B, I, J
keep their seeds. From z8b.rs, lane_kernel, slice_from, rank_of and d_own
are copied verbatim. New code: Lanes (the balanced sources), lane_elim,
Relations (S1/S2/S2u/S3_u/low/ia from fold::dual_fold,
encoder::exact_final_encoder and fold::quarter), the left-kernel report,
projection ranks, the OT/OT'/F5 passes, the D-high, G-low and PR6/PR7
blocks, and the transport checks (ROW_TO_COEFFICIENT = z5::transport;
row 0 inactive; coefficients < 89 inactive).
All 35 CHALLENGE lines match probe-C.log, and so do the 25 terminal
triples of A.

9. Runs and receipts
--------------------
Host dombarker@100.108.41.90, staging
/home/dombarker/project-offloads/aspis-z8c-20261015/ (fresh; repo/ = rsync of
Cargo.toml, crates/aspis-{core,statement,prover}, z4/). No other aspis scope
was active at launch, and the reserved MemoryMax was 4 GiB. Release profile
opt-level=3 with overflow-checks; rustc 1.94.1 (e408947bf 2026-03-25).
The Lean workspace and its lock were not touched.

  cd /home/dombarker/project-offloads/aspis-z8c-20261015/repo
  /usr/bin/time -v -o ../preflight{,2}-time.txt systemd-run --user --scope --unit=aspis-z8c-preflight{,2} \
    -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
    python3 docs/research/v8-r0-zk-20261009/z4/run-z8c.py \
    --out /home/dombarker/project-offloads/aspis-z8c-20261015/preflight{,2}-evidence --preflight
  /usr/bin/time -v -o ../full-time.txt systemd-run --user --scope --unit=aspis-z8c-full \
    -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
    python3 docs/research/v8-r0-zk-20261009/z4/run-z8c.py \
    --out /home/dombarker/project-offloads/aspis-z8c-20261015/full-evidence --vectors 5 --jobs 5

 scope / target            exit  wall s            peak child RSS KiB  cgroup peak B    swap
 preflight / compile       0     55.883            547,088             888,672,256      0
 preflight / A-0           0     261.114           308,400             888,672,256      0
 preflight2 / A-0          0     278.793           312,788             343,576,576      0
 full / compile            0     0.061             28,856              26,628,096       0
 full / 35 jobs            0     474.2 - 611.8     303,600 - 313,952   1,585,782,784    0
 full scope total          0     1:04:03 (time -v), max RSS 313,952 KiB, swaps 0

There are 36 per-process receipts in the full scope (evidence-Z8c.json),
all exit 0 with swap 0. Up to 5 jobs ran concurrently. 209 source SHA-256s
are recorded and all match this worktree. Local work was `cargo check`
only. No Lean was run, so #print axioms does not apply.

Artifacts: z8c.rs, run-z8c.py, summary-Z8c.json, evidence-Z8c.json,
probe-Z8c.log (35 job logs concatenated), z8c-runs/ (driver logs, compile
logs, time -v outputs, both preflight logs).
