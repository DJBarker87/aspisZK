# Z8b — decomposition check (lead copy of the agent's FINDINGS-Z8b.txt; D20‴.3, accepted 2026-10-13)

```text
Z8b -- decomposition check: PCS cancellation (P) and round spanning (Q) (LOG D20‴.3)
==================================================================================

Base eb4e80c08 (origin/v8-reference). Branch codex/z8b-decomposition-20261013.
Exact M31/QM31/WideExact computation on Z8's structure-(A) vectors 0..4 with
Z8's WideExact opening challenges and real linearPayload silence coordinates.
Not a Lean proof; no Lean or production source changed. Lead converts to .md.

STOP: none. Every number below was identical on all 5 vectors.

0. Counting note (differs from the job text)
--------------------------------------------
A K4-valued lane (G, D) has 94 own-silence functionals, not 112: 3 point
claims + 1 extra claim + 2 OOD + 88 opened symbols, each K4-valued, i.e.
94 x 4 = 376 M31 limbs (Z8's raw_c ext rows minus the inactive entry). The
"112" of an F-lane counts limbs (12 claim + 4 extra + 8 OOD + 88 opened). So
the (1) functional count is 2,112 + 376 = 2,488, not 2,112 + 448 = 2,560, and
the G/D per-lane maximum is 376, not 448.

1. Per-lane own-silence functional ranks (sources = all 1,024 rows)
-------------------------------------------------------------------
 mask-only lanes 16..25 (F words, 112 F-functionals): 112 each (all 10)
 G (K4 words, 376 limbs):                              376
 G with its inactive-row sum added (380 limbs):        380
 D (K4 words, 376 limbs):                              376
 D restricted to coefficients 0..55 (224 sources):     224
 D restricted to coefficients 56..1023 (3,872 sources): 372
 (The mask-only lanes share one functional set, raw_c base rows 1..112, on
 Z8's random 22-fibre query set; G and D share raw_c ext rows 1..94.)

2. (P) PCS cancellation block: D's coefficients 56..1023
--------------------------------------------------------
 Columns: D sources x*e_{pi^-1(k)}, k = 56..1023, x in the tower basis
 (3,872 = 968 K4 coordinates). Functionals: the 264 batched WideExact
 coordinates (2,112 limbs; gamma^28 weighting) and D's 376 own limbs.
 D's round contribution (tail_row) is zero on all these rows (checked).

                         rank   batched   D-own   .inactiveSum  .opening+.final
                                only      only    only (of 8)   only (of 2,104)
 D 56..1023              2,184  2,000     372     4             1,996
 + G inactive-row sum    2,188  2,004     372     8             1,996
   (4 extra columns: gamma^27 * x in .inactiveSum only)
 functionals             2,488  2,112     376     8             2,104

 * D alone reaches a 4-dimensional (one K4-line) subspace of .inactiveSum;
   adding G's inactive-row sum gives all 8 limbs.
 * The block is not full rank: 2,184 (2,188 with G) of 2,488. The batched
   part alone has rank 2,000 (2,004) of 2,112; D-own has 372 of 376.

3. (Q) Round spanning: round image of
   {mask-only words in their own-silence kernels} + {G words in G's
   own-silence kernel with zero inactive-row sum} + {D words on coefficients 0..55}
------------------------------------------------------------------------
 Generators: 9,120 mask kernel + 3,716 G kernel + 224 D(0..55).
 (No batched or D-own condition imposed in this step.)

 round j                 0    1    2    3    4    5    6    7    8    9   total
 initial retained      112  112  112  112  112  112  112  112  112  112   1,084
 initial zero          108  112  112  112  112  112  112  112  112  112   1,080
 Per limb: 28 each (27 at round 0 with initial zero).
 Chain0 basis (1,080 normalized units) against the initial-zero image:
 excess 0. Z4c (i') targets against it: 5/5 per vector, 25/25.
 (The image is 1,084 / 1,080 rather than 1,080 / 1,076 because D(0..55)
 is unconstrained here, so the terminal value is not forced to 0.)
 Intersection of the (Q) generators alone with silence (batched = 0 and
 D-own = 0, initial zero): 988.

4. (Q) + (P) assembled: silent subspace of the (Q) generators plus D's
   coefficients 56..1023 (silence = batched 2,112 + D-own 376 limbs zero)
------------------------------------------------------------------------
 span rank 3,376; silence pivots 2,296; initial retained 1,080; silent 1,076
 (Z8 structure (A): 1,076).

 round j                 0    1    2    3    4    5    6    7    8    9   total
 silent                108  112  112  112  112  112  112  112  112  108   1,076
 initial retained      112  112  112  112  112  112  112  112  112  108   1,080
 Per limb: 28 each (27 at rounds 0 and 9 in the silent row).

 Chain0 basis: excess 0. Z4c (i'): 25/25. Derivative diagnostic: 25/25.
 Supports and pivots [].

5. Interpretation (factual)
---------------------------
* The assembled modular subspace reaches the same silent rank as Z8's full
  construction (1,076) with all (i') targets contained, on all 5 vectors:
  on these vectors the decomposition loses nothing.
* (Q) alone spans the full initial-zero round space (1,080) and contains
  Chain0 and the (i') targets before any PCS condition is imposed.
* (P) as a rank statement does not hold in the form "full rank 2,560":
  the functional count is 2,488, the measured rank is 2,184 (2,188 with G's
  inactive-row sum). The batched coordinates restricted to D(56..1023) have
  rank 2,000 of 2,112, and D's own functionals 372 of 376 there. The
  .inactiveSum shortfall without G is exactly one K4-line (4 limbs), as
  D20‴.3 anticipated; with G it is full.
* Silence pivots of the assembled span: 2,296 (= 2,488 - 192). The
  assembled silent rank equals Z8's although the (P) block is rank-deficient.

6. Code
-------
z8b.rs is a module of probe.rs dispatched by `--z8b` (probe.rs changes: the
`mod z8b` declaration and one dispatch line). Its first part is copied
verbatim from z8.rs (trial replay, alpha helpers, round_polys, Proj,
WideExact opening challenges, Lean totalWeights, column-wise
prover::quotient unit functionals, Ctx, carry, scale, report,
decomposition_check -- the whole-column pipeline check passes on every job).
New: lane_kernel (z8's lane_stage with variable carry width and a sink),
gen3, the (P)/(Q)/assembled sections. Called unchanged from probe.rs: Ech,
initial_zero, copied_ech, summarize, pass_count, raw_c, tail_row, round_row,
compute_targets, normalized, normalize_d, final_value, balance_trace,
real::instances. All 5 CHALLENGE lines and 25 terminal triples match
probe-C.log.

7. Runs and receipts
--------------------
Host dombarker@100.108.41.90, staging /home/dombarker/project-offloads/aspis-z8b-20261013/
(repo/ = rsync of Cargo.toml, crates/aspis-{core,statement,prover}, z4/).
No other aspis scope active at launch; reserved MemoryMax 4 GiB.
Release profile opt-level=3, overflow-checks; rustc 1.94.1 (e408947bf 2026-03-25).

  cd /home/dombarker/project-offloads/aspis-z8b-20261013/repo
  /usr/bin/time -v -o ../preflight-time.txt systemd-run --user --scope --unit=aspis-z8b-preflight \
    -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
    python3 docs/research/v8-r0-zk-20261009/z4/run-z8b.py \
    --out /home/dombarker/project-offloads/aspis-z8b-20261013/preflight-evidence --preflight
  /usr/bin/time -v -o ../full-time.txt systemd-run --user --scope --unit=aspis-z8b-full \
    -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
    python3 docs/research/v8-r0-zk-20261009/z4/run-z8b.py \
    --out /home/dombarker/project-offloads/aspis-z8b-20261013/full-evidence --vectors 5 --jobs 5

 scope / target          exit  wall s           peak child RSS KiB  cgroup peak B    swap
 preflight / compile     0     52.688           545,980             886,128,640      0
 preflight / A-0 (no targets)
                         0     306.705          208,544             886,128,640      0
 full / compile          0     0.064            28,852              26,935,296       0
 full / A-0..A-4         0     438.1 - 516.7    216,380 - 217,884   1,077,284,864    0
 full scope total        0     516.813 (driver), 8:36.92 (time -v), max RSS 217,884 KiB, swaps 0

208 source SHA-256s recorded; all match this worktree. Local work: `cargo
check` only. No Lean run; #print axioms not applicable.

Artifacts: z8b.rs, run-z8b.py, summary-Z8b.json, evidence-Z8b.json,
probe-Z8b.log, z8b-runs/ (driver log, compile logs, time -v outputs,
preflight log).
```
