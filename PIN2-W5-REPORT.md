# PIN2 W5: verifier intermediate values for the joint accepted fixture

Worker W5, branch `fix/pin2-lean-20261110`, worktree `/Users/dominic/ZK/.worktrees/pin2-lean`. The evidence directory is `docs/research/100bit-spend-path-20261013/evidence/pin2-w5-20261111/`, and the compile table is `PIN2-W5-COMPILE.tsv` at the worktree root. The dumper lives in `/Users/dominic/ZK/.worktrees/pin2-candidate/tools/pin2-w5-dump` (commit `46dc0d2bc4c` on `codex/pin2-candidate-20261110`, not pushed, lead tooling, not shipped source). Every Lean compile was one local `lean -M7000 -DElab.async=false` process under a 180 s alarm. Each one started only when no other Lean process was running, with `LEAN_PATH = overlay-PIN2-W4 : overlay-PIN2 : objs : base`. Nothing ran on the build host, nothing was pushed, no symlink was created, and objs, base and overlay-PIN2 were not written. I did not touch W3c's uncommitted files.

In short: there is now a native dumper. It reproduces the recorded PIN2 stage-1 checkpoint byte for byte, and stage 2 accepts. A dump of the 26 October inputs, made with the same dumper built against the frozen 4bb3b3f library, shows exactly where the 26 October fixture's transcript values came from: every one is a native verifier intermediate value. With that dump as input, the original generators reproduce 207 release modules and 70 generator data files byte for byte. On the PIN2 dump they produce 179 changed modules. 96 of those, plus 2 unchanged generic modules they need, are compiled with standard axioms only. The other 83 are blocked, mostly by the same W3c root that W4 reported.

## 1. Provenance of the value format

W4 wrote that the transcript-dependent generators read diagnostic JSON that no committed script writes. For most of those files that is not quite right. Here is what each one actually is:

- `JFm_WINDOWS.json` is written by `evidence/joint-fixture11-20261026/JFm_generate.py`. That script recomputes the semantic transcript in Python with hashlib, from the proof data modules and the seed in `JFp_SHA_INPUT.json`. The JFu row-25/26 generators read it.
- `JFw_POWERS.json` is written by `JFw_generate.py`, and the powers are taken of a **hard-coded** `G=[...]`. `G` is gamma.
- `JFw_HEADS.json` and `JFw_RAW.json` are written by `JFw_generate_heads.py` and `JFw_generate_raw.py`. Both are derived from POWERS and proof bytes.
- `JFs_TX2_POINT_VALUES.json` is written by `JFs_TX2_generate_points.py`, from a **hard-coded** `queries=[...]` list (queries 10..21).
- `JFr_coefficients.json` has no committed writer.
- `JFw_NUMERIC_PREFLIGHT.json` has no committed writer either. It is labelled "Python arithmetic preflight only".
- The row-25 split drafts `JFm_UNCHECKED/JFm_Q25Block00..58`, `SplitAggregate` and `SplitReads` have no committed writer. `PIN2W5_split25.py` rebuilds all 61 of them byte for byte from the archived `JFm_Q25Hashes.lean.txt`.
- `NDO_JFm_Coordinates` is handwritten, with 25 QM31 literals.

No committed Rust dumper exists. The `trace` module (`crates/aspis-r1-cost-probe/src/trace.rs`) records only under the host `prover` feature, and only `examples/*_gate.rs` consume it, for equivalence checks. Nothing on research ever used it to write fixture values.

To settle the provenance I built the same dumper against `4bb3b3f` crates, in a scratch `git archive` tree. The only change was in the manifest: I dropped the optional `aspis-z4b-probe` dependency, which serves the unused `r1p-check` feature (`provenance-26oct/4bb3b3f-scratch-manifest.diff`). I then ran it on the 26 October proof `55386c50…`, statement `f6bcd494…` and checkpoint `6c9f774d…`. Its stage-1 output equals the `JFx_DataCheckpoint00` bytes, stage 2 accepts, and the seed is `e4a92261…751e` (`JFr_SeedBoundary`). `PIN2W5_provenance.py` compares the fixture literals with that dump (`provenance-26oct/PROVENANCE.json`, 20 checks, all equal):

| 26 October fixture value | Native source (dump record) |
| --- | --- |
| `JFm_WINDOWS.json` frame/before/absorbed/read/after, 27 rows | SHA calls of `r1_wire::SemanticTranscript`: `H(state,[0,0xa0+row],framed)`, `H(absorbed,[1])`, `H(absorbed,[2])` |
| `JFm_WINDOWS` coordinates rows 0..24, `NDO_JFm_Coordinates.value00..24` | tag 0 = `challenges.with_alphas` (lambda, chi, theta, zc[10], mu, eta, alpha[10]) |
| `JFr_coefficients.json` running/boundary/value | tag 1 index 3r+j (`round_checks`) |
| `JFr_coefficients.json` alpha | tag 0 index 15+r; coefficients = proof[offset:offset+448] as 28 QM31 |
| `G` in `JFw_generate.py` | tag 4 index 27 (gamma, `Transcript::scalar` row 27) |
| `queries` in `JFs_TX2_generate_points.py` | tag 5 indices 10..21 |
| `JFw_NUMERIC_PREFLIGHT` dots, circle (= selected) | tx2 tag 9 indices 40..43, tx2 tag 10 index 20 (query 10); tails = dots − JFw_HEADS (Python) |
| checkpoint gamma [176,208), queries [320,408), semantic alphas [408,568), z [568,632), claim [632,664), rhs [664,696), state [80,112) | tags 4/27, 5, 0/15..24, 3, 14/7, 11/9, final opening-transcript state |

The dump format (`PIN2W5_dump.py`) has three record types:

- `V <stage> <seq> <tag> <index> <hex32>` for each `trace::value`. hex32 is `WideExact::to_le_bytes`, i.e. 8 LE u32 limbs. A QM31 is the first 4 limbs.
- `H <stage> <seq> <part lengths> <input hex> <output hex>` for each SHA-256 call.
- `R` lines for results.

`PIN2W5_derive.py` turns a dump into `PIN2W5_VALUES.json`. That file holds the seed, the 27 semantic windows, the opening transcript (rows 27–32, the 8 query blocks, and which advance state rho resumes from), and every tag by index. The tags are:

- 0: semantic samples
- 1: round checks
- 2: terminal and masked terminal
- 3: z0/z1
- 4: opening scalars (27 gamma, 28 kappa, 29 alpha0, 30 alpha1, 32 rho)
- 5: queries
- 9: four dots
- 10: circle/line folds
- 11: rhs
- 12/13: weights and basis
- 14: claim parts
- 15: relation rounds
- 16: pair/claim
- 17: final dot/rhs
- 6/7/8: tx2 pairing weights and parts

`PIN2W5_hardcoded.py` (`HARDCODED.json`) scanned all 365 generator scripts in the joint-fixture*/fixture-tx2* directories for literals ≥ 2^16 that equal a 26 October native limb. 21 scripts embed native values: gamma (tag 4) in JFw/JFz, query indices (tag 5) in JFo/JFn/JFs_TX2/JGc/JGf/JGk/JGp/JGr/JGu/JGw, and round-check/terminal/challenge limbs (tags 0/1/2) in JGd and JGn. Query indices below 65,536 are not caught by that threshold.

## 2. The dumper and its hashes

`tools/pin2-w5-dump` is a standalone crate whose `Cargo.lock` is copied from the root workspace lock. No version outside it is resolved (checked: all 34 locked packages are in the root lock). Its dependencies are `aspis-core` (r0), `aspis-statement` (r0, pool-v1-kernel) and `aspis-r1-cost-probe` with `optimized-terminal` (the program's feature) plus `prover`. `prover` is the only switch that enables `trace::value`. The verifier crates are unchanged from `c7593d23fdc` (`git diff c7593d23fdc HEAD -- crates programs` is empty).

The run follows `r1_pool_adapter_owned`:

1. Stage 1 decodes and validates the 1,880-byte statement, then calls `candidate::tx1(statement.semantic_public(), statement bytes, proof, k = 10, …)`. This is tag `[3,10]`.
2. Stage 2 calls `tx2_authenticated(encode(statement), proof, recorded checkpoint, …)`. The re-encoded statement equals the account bytes, which is checked.
3. A strict `tx2` runs as a second check.

The digest is SHA-256 over the concatenated parts, the same as `SolanaDigest`/`hashv`, wrapped so that each call is recorded.

| Item | sha256 |
| --- | --- |
| `src/main.rs` | `0266b75d53684cf902174fef1d6ebfa8e4bd72877d10d01e68b47be8bb0c4067` |
| `Cargo.toml` | `bdbe90d6598cec14ac589426c3fc3287e9630419bd24736da86ed8e65990c7c2` |
| `Cargo.lock` | `c3b5186b754d078eae3f2acc4f3026c8ed34f9998ff7a7a7ada8abc4e13be493` |
| debug binary | `10b42095556481d9e0fa680a87f254f07c2222ec630759994a75a7e5e54165a5` |
| release binary | `ed83fb690152abf843f29fbdf8e704c6046f7a019ef0187fa2ce8089dbd1cd1e` |
| `PIN2W5_DUMP.txt` (PIN2 transfer, 1.43 MB) | `7a017066135a9e6aa6c8a28525965e8bd4dc22c9c395287360c2cfc440e86f08` |
| `PIN2W5_VALUES.json` | `ee1c66dfa89af91f624d0a7f2150eb74c676584032413107cbf0652cec05ddbc` |
| 4bb3b3f debug binary (scratch) | `a4e55e2e142bf294f967e0c6d7250fcf982fce61f4f677855198b02d56fe7d13` |
| `provenance-26oct/DUMP-26OCT-4bb3b3f.txt` | `1479bbe9e0a4866ed3ecf96f42a68c812914772f0b63e390061aebdcfb7feaa9` |

The PIN2 run took 0.37 s wall with 6.5 MB RSS (debug build). The release build's dump is identical, apart from the `debug_assertions` line. The dump has 1,446 tx1 values, 9,253 tx2 values and 580 + 530 SHA calls. The inputs are W4's `transfer-proof.bin` `354a754d…64cd`, `transfer-statement.bin` `64eb9b43…c9fe` and `transfer-checkpoint.bin` `27bcbe25…1652`. My copies in `inputs/` hash identically to W4's `inputs/SHA256SUMS`.

## 3. Cross-checks

`PIN2W5_crosscheck.py` uses hashlib only and writes `CROSSCHECK.json`. All 24 checks pass:

- The Rust `semantic_public().public_bytes()` (1,520 B) equals W4's independent Python-model public bytes.
- The frame `DOMAIN ‖ 0 ‖ le32 1520 ‖ public ‖ proof[16:48]` is 1,595 B and equals W4's frame.
- sha256 of that frame equals the native seed `17667969372a21c5833136bf944e8cc7fb0ab0e53ea40acfec66ca0afdd050a1`.
- **First semantic sample.** Row 0 frame = `proof[48:53]` = 5 zero bytes. absorbed = H(seed‖00 a0‖frame), read = H(absorbed‖01). lambda = base-P digits of read = `[1526197484, 972223295, 1344894819, 1842842573]` = tag 0 index 0.
- The whole 27-row semantic chain recomputed in Python equals the native chain. The 25 samples equal the base-P digits of the 25 reads.
- **Checkpoint fields.** The native stage-1 output equals the recorded 1,768 bytes. [16,48) = sha256(proof), [48,80) = sha256(statement), [112,144) = c1 root, and the trailer = sha256("UNPROVED:R1:checkpoint" ‖ ck[:1736]). The semantic alphas [408,568) equal the Python-sampled reads 15..24, the queries [320,408) equal tag 5, gamma [176,208) equals tag 4/27, and the state [80,112) equals the final opening-transcript state. The opening state0 = sha256("UNPROVED:R1:PRIVATE-SALTED:P3" ‖ 2 ‖ semantic state after row 26).
- Stage 2 accepts, both authenticated and strict.
- **Against the raw devnet recording** (`pin2-run/receipts/PIN2_spend/transfer-stage1-recording.json`, not W4's files): the instruction is `030a` and meta.err is null. Proof account data[688:] = proof, the statement account = statement, and the post-stage-1 checkpoint account = checkpoint.

The PIN2 queries are `[46430, 76575, 251221, 185082, 132668, 55341, 88718, 248686, 152194, 172017, 86898, 117873, 189155, 110201, 151183, 177645, 179723, 126205, 162719, 101707, 156707, 243786]`.

## 4. Regeneration

`PIN2W5_regen.py` reruns 13 original generators plus helper `JFm_input.py`, taken verbatim from research in a scratch tree:

- JFp_generate_queries `6b233348d064`
- JFm_generate `df52c749907b`
- JFm_sources `18db3b486a2a`
- JFr_generate_arithmetic/bytes/decoders `788b868b742d`/`318cb5d7ecf2`/`6f2c8cb6517e`
- JFw_generate `a06d094ae4d0`
- JFs_TX2_generate_points `533f72ca9320`
- JFu_claims/mask/sources/split/split26 `e24f1c11b9a7`/`ac671d408a5b`/`fc6907f63c34`/`a6d0e57273fa`/`fe3ededdcf9a`

The substitutions are only the dump-sourced inputs from the table in section 1, plus W4's PIN2 data/scan modules and PIN2 seed JSON. Outputs get the release import header (NDO_ names).

- **`check` mode** feeds the 26 October *native dump*, not the committed JSON, through the same path. It reproduces all 207 release modules and all 70 other outputs byte for byte. Those 70 are JFm_WINDOWS, JFr_coefficients (asserted), JFw_POWERS, JFs_TX2_POINT_VALUES, JFp_QUERY00_DIAGNOSTIC, JFu_WINDOWS_PLAN and the 61+4 archived row-25/26 drafts.
- **`pin2` mode** gives 179 changed modules (`sources/`) and 28 text-identical ones. The regenerated data files are in `generated/`.
- `PIN2W5_shape.py` (`SHAPE.json`) confirms that the generator-computed PIN2 windows equal the native windows, its coordinates equal tag 0, POWERS[1] equals gamma, and the geometry queries equal tag 5.

**Shape changes.** No theorem statement changes length or block count. The frame and row geometry are unchanged, so every Absorb/Reads/Hashes has the same block count as in October. Two kinds of proof-text shape differ, both data-driven by the original generators:

- 19 `JFw_TX2_Pkk` modules have `lane` lemmas stated as `(-n : ZMod P) = m` instead of `(n : ZMod P) = m`. The generator prints the lane's signed representative.
- 9 `JFs_TX2_Geo` modules have one extra or one fewer full table-read proof, because whether u, ⌊u/4⌋·4 and ⌊u/4⌋·4+3 coincide depends on the query value.

The named statements (`sourceK : fibre_point … u = ok valueK`, `checked`, `powNN`) keep their shape. The length changes 1455→1520 and 1530→1595 are not in this layer; W4 owns them in the statement/seed layer.

## 5. Modules compiled

98 compiles, all exit 0, none failed. Every `#print axioms` line names only `propext`, `Classical.choice` and `Quot.sound`, and there is no sorry. Total wall time is 667 s, the longest compile 33 s (`JFm_QnnHashes`), and peak RSS 6.38 GB (`NDO_JFu_Q25Aggregate`, under the 7000 MB heap cap). Swap is not measured on macOS. The revision column is worktree HEAD `23c6ba1ad7e`, with sources from this branch's evidence directory (committed afterwards).

What is compiled:

- **In the release closure (52):** `NDO_JFp_Query00Absorb/Read/Ratchet`, `NDO_JFm_Q01..14Absorb/Reads`, `NDO_JFm_Q15..24Hashes`, `NDO_JFu_Q25Block00`, `Window01..57` (8), `Q25Aggregate` and `Q25Reads`. That is the whole SHA certificate chain of the PIN2 semantic transcript from the seed through row 25.
- **Outside the release closure (44 changed + 2 unchanged generic):** `NDO_JFm_Coordinates`, `NDO_JFr_Data00..09`, `Boundary00..09` and `Horner00_0..09_1`, `NDO_JFu_Q26Window00/08`, `Q26Reads`. The generic ones are `NDO_JFr_HornerTrace` and `NDO_JFu_Q26Aggregate` (unchanged release source, rebuilt because their imports changed).

```
id            module                     exit  wall_s  peak_rss_bytes
PIN2W5_C0001  NDO_JFp_Query00Absorb      0    15.76  2693971968
PIN2W5_C0002  NDO_JFp_Query00Read        0     3.08  2693316608
PIN2W5_C0003  NDO_JFp_Query00Ratchet     0     3.05  2692169728
PIN2W5_C0004  NDO_JFm_Q01Absorb          0     2.62  2622406656
PIN2W5_C0005  NDO_JFm_Q01Reads           0     3.81  2671198208
PIN2W5_C0006  NDO_JFm_Q02Absorb          0     4.13  2775564288
PIN2W5_C0007  NDO_JFm_Q02Reads           0     3.84  2678161408
PIN2W5_C0008  NDO_JFm_Q03Absorb          0     2.64  2623324160
PIN2W5_C0009  NDO_JFm_Q03Reads           0     3.88  2671017984
PIN2W5_C0010  NDO_JFm_Q04Absorb          0     2.66  2625568768
PIN2W5_C0011  NDO_JFm_Q04Reads           0     3.88  2678489088
PIN2W5_C0012  NDO_JFm_Q05Absorb          0     2.70  2623307776
PIN2W5_C0013  NDO_JFm_Q05Reads           0     3.93  2678538240
PIN2W5_C0014  NDO_JFm_Q06Absorb          0     2.66  2625306624
PIN2W5_C0015  NDO_JFm_Q06Reads           0     3.88  2678554624
PIN2W5_C0016  NDO_JFm_Q07Absorb          0     2.66  2622586880
PIN2W5_C0017  NDO_JFm_Q07Reads           0     3.91  2677473280
PIN2W5_C0018  NDO_JFm_Q08Absorb          0     2.67  2625142784
PIN2W5_C0019  NDO_JFm_Q08Reads           0     3.88  2677538816
PIN2W5_C0020  NDO_JFm_Q09Absorb          0     2.72  2625667072
PIN2W5_C0021  NDO_JFm_Q09Reads           0     3.91  2677522432
PIN2W5_C0022  NDO_JFm_Q10Absorb          0     2.67  2625421312
PIN2W5_C0023  NDO_JFm_Q10Reads           0     3.91  2678358016
PIN2W5_C0024  NDO_JFm_Q11Absorb          0     2.67  2625601536
PIN2W5_C0025  NDO_JFm_Q11Reads           0     3.92  2677407744
PIN2W5_C0026  NDO_JFm_Q12Absorb          0     2.92  2626699264
PIN2W5_C0027  NDO_JFm_Q12Reads           0     4.34  2678849536
PIN2W5_C0028  NDO_JFm_Q13Absorb          0     2.71  2625355776
PIN2W5_C0029  NDO_JFm_Q13Reads           0     3.95  2678259712
PIN2W5_C0030  NDO_JFm_Q14Absorb          0     4.11  2775302144
PIN2W5_C0031  NDO_JFm_Q14Reads           0     3.93  2677653504
PIN2W5_C0032  NDO_JFm_Q15Hashes          0    32.98  4199120896
PIN2W5_C0033  NDO_JFm_Q16Hashes          0    32.99  4199940096
PIN2W5_C0034  NDO_JFm_Q17Hashes          0    32.87  4199383040
PIN2W5_C0035  NDO_JFm_Q18Hashes          0    33.66  4200513536
PIN2W5_C0036  NDO_JFm_Q19Hashes          0    32.47  4187979776
PIN2W5_C0037  NDO_JFm_Q20Hashes          0    30.50  4183359488
PIN2W5_C0038  NDO_JFm_Q21Hashes          0    30.41  4199383040
PIN2W5_C0039  NDO_JFm_Q22Hashes          0    30.32  4183293952
PIN2W5_C0040  NDO_JFm_Q23Hashes          0    30.20  4199694336
PIN2W5_C0041  NDO_JFm_Q24Hashes          0    30.26  4198809600
PIN2W5_C0042  NDO_JFu_Q25Block00         0     2.73  2623012864
PIN2W5_C0043  NDO_JFu_Q25Window01        0    12.05  2983444480
PIN2W5_C0044  NDO_JFu_Q25Window09        0    12.07  2970681344
PIN2W5_C0045  NDO_JFu_Q25Window17        0    12.04  2970910720
PIN2W5_C0046  NDO_JFu_Q25Window25        0    12.07  2986377216
PIN2W5_C0047  NDO_JFu_Q25Window33        0    12.05  2986426368
PIN2W5_C0048  NDO_JFu_Q25Window41        0    12.07  2987425792
PIN2W5_C0049  NDO_JFu_Q25Window49        0    12.10  2987130880
PIN2W5_C0050  NDO_JFu_Q25Window57        0     3.84  2668085248
PIN2W5_C0051  NDO_JFu_Q25Aggregate       0    14.20  6380961792
PIN2W5_C0052  NDO_JFu_Q25Reads           0     3.99  2671738880
PIN2W5_C0053  NDO_JFm_Coordinates        0     5.27  3284172800
PIN2W5_C0054  NDO_JFr_Data00             0     1.89  2581495808
PIN2W5_C0055  NDO_JFr_Boundary00         0     2.16  2592309248
PIN2W5_C0056  NDO_JFr_Data01             0     1.90  2581676032
PIN2W5_C0057  NDO_JFr_Boundary01         0     2.16  2593013760
PIN2W5_C0058  NDO_JFr_Data02             0     1.87  2580496384
PIN2W5_C0059  NDO_JFr_Boundary02         0     2.16  2593603584
PIN2W5_C0060  NDO_JFr_Data03             0     1.88  2581135360
PIN2W5_C0061  NDO_JFr_Boundary03         0     2.15  2592522240
PIN2W5_C0062  NDO_JFr_Data04             0     1.90  2581807104
PIN2W5_C0063  NDO_JFr_Boundary04         0     2.14  2592620544
PIN2W5_C0064  NDO_JFr_Data05             0     1.89  2582331392
PIN2W5_C0065  NDO_JFr_Boundary05         0     2.16  2593423360
PIN2W5_C0066  NDO_JFr_Data06             0     1.90  2581479424
PIN2W5_C0067  NDO_JFr_Boundary06         0     2.17  2591916032
PIN2W5_C0068  NDO_JFr_Data07             0     1.89  2581266432
PIN2W5_C0069  NDO_JFr_Boundary07         0     2.16  2593243136
PIN2W5_C0070  NDO_JFr_Data08             0     1.90  2582315008
PIN2W5_C0071  NDO_JFr_Boundary08         0     2.16  2592784384
PIN2W5_C0072  NDO_JFr_Data09             0     1.88  2581151744
PIN2W5_C0073  NDO_JFr_Boundary09         0     2.15  2592833536
PIN2W5_C0074  NDO_JFu_Q26Window00        0    12.10  2986213376
PIN2W5_C0075  NDO_JFu_Q26Window08        0    12.09  2985426944
PIN2W5_C0076  NDO_JFr_HornerTrace        0     1.51  2572582912
PIN2W5_C0077  NDO_JFr_Horner00_0         0     2.15  2594258944
PIN2W5_C0078  NDO_JFr_Horner00_1         0     2.15  2592784384
PIN2W5_C0079  NDO_JFr_Horner01_0         0     2.18  2594652160
PIN2W5_C0080  NDO_JFr_Horner01_1         0     2.20  2592849920
PIN2W5_C0081  NDO_JFr_Horner02_0         0     2.20  2594504704
PIN2W5_C0082  NDO_JFr_Horner02_1         0     2.20  2592243712
PIN2W5_C0083  NDO_JFr_Horner03_0         0     2.21  2594324480
PIN2W5_C0084  NDO_JFr_Horner03_1         0     2.19  2593406976
PIN2W5_C0085  NDO_JFr_Horner04_0         0     2.20  2595241984
PIN2W5_C0086  NDO_JFr_Horner04_1         0     2.22  2593538048
PIN2W5_C0087  NDO_JFr_Horner05_0         0     2.22  2593832960
PIN2W5_C0088  NDO_JFr_Horner05_1         0     2.20  2592899072
PIN2W5_C0089  NDO_JFr_Horner06_0         0     2.21  2594471936
PIN2W5_C0090  NDO_JFr_Horner06_1         0     2.22  2592014336
PIN2W5_C0091  NDO_JFr_Horner07_0         0     2.22  2593931264
PIN2W5_C0092  NDO_JFr_Horner07_1         0     2.22  2592931840
PIN2W5_C0093  NDO_JFr_Horner08_0         0     2.22  2595405824
PIN2W5_C0094  NDO_JFr_Horner08_1         0     2.23  2593128448
PIN2W5_C0095  NDO_JFr_Horner09_0         0     2.23  2594160640
PIN2W5_C0096  NDO_JFr_Horner09_1         0     2.23  2592587776
PIN2W5_C0097  NDO_JFu_Q26Aggregate       0     4.65  3597008896
PIN2W5_C0098  NDO_JFu_Q26Reads           0     3.98  2675933184
```

## 6. Modules still blocked, and why

83 regenerated sources are not compiled (`BLOCKED.json`, from `PIN2W5_blocked.py`). The blockers fall into three groups.

**In the release closure, by the W3c root (W4 section 3).** These are `NDO_JFm_Q01..24Source` (24), `NDO_JFu_ClaimsData` and `ClaimsBytes0..3` (5), and `NDO_JFu_Q25InputBase` (1). Every one reaches `NDO_JFp_SHADigest` → `JFp_InitBytes`/`JFr_SeedBoundary` → `JFs_ExactInitialization`, and/or `NDO_JFw_NativeRow*` → `JFw_Frames` → `RPz7_PSem_*`. The `PIN2_NEWGATE_r0` / `instDiscriminantErrorIsize` import clash blocks both chains. The 5 text-identical `ClaimsDecode` modules come after them.

**Outside the release closure.** These are `NDO_JFr_Bytes00..09` (statement layer via `JFr_EncodedCell` → `DecodeCell`), `NDO_JFs_TX2_Geo10..21`, `NDO_JFw_TX2_P01..28`, `NDO_JFu_MaskInputs` and `NDO_JFu_Q25/Q26Source`. Their generic dependencies (`JFs_TX2_PointCall` → `RPt_JFs_TX2_ArrayRead`, `JFw_TX2_ValueUnique` → `DotsExplicit` → …) were never built in the L187 closure, and they lead back into W3c-blocked RPt_/RPu_ modules. These are research fixture modules, not dependencies of the headline.

**Not regenerated.** Only the TX2 families JFq/JFo/JFn/JFr_TX2/JFv_TX2, JFw heads/raw/dots/circle/tails, and the later JFz/JG*/JH* generators were left unregenerated. Their native inputs are now identified and available in `PIN2W5_VALUES.json` (`HARDCODED.json`; NUMERIC_PREFLIGHT = tx2 tag 9/10 plus Python heads). Most of them, however, also read literals of earlier handwritten Lean modules (for example `JFr_TX2_Tails10`), so each needs its own check-mode reproduction before substitution. Only `JFn_LineTotal`, `JFn_ScaleTotal` and `JFr_TX2_CircleTotal` from those families are in the release closure. The rows-25/26 `JFm_Q25/Q26Hashes` monoliths were regenerated as drafts only, because the October one timed out at 180 s. Their split replacements are what I compiled.

## 7. overlay-PIN2-W4 after

The directory now has 249 regular files and no links. W4's 151 objects are unchanged (before list `OVERLAY-PIN2-W4.before.sha256` = W4's list; no line removed). 98 objects are added. Full list: `docs/research/100bit-spend-path-20261013/evidence/pin2-w5-20261111/OVERLAY-PIN2-W4.after.sha256`. The added objects:

```
61dea69fc9c27a9118eac34f740bf6ff2ccaa40c18d4e5d97e69d5d7bd0bcc0d  NDO_JFm_Coordinates.olean
b11032c4cdc6bbb609b9e5bb7f446c75441bd6f940da953d306bf8fab4ea2713  NDO_JFm_Q01Absorb.olean
9d518e6e34303068457d9d1de8e9a3def9f50ce182f1ae482b09077c20b6a1fa  NDO_JFm_Q01Reads.olean
4561ffe43d015390adc121123a153a46efabff5355c87ba36853f98a5bba10ed  NDO_JFm_Q02Absorb.olean
b99ff55823a02842ae53de005248f3d8d83e94da3a942f0cf9839e4972cac806  NDO_JFm_Q02Reads.olean
f6e310ba9c9a70cb6cbd8e8d5724d40ac9c94e0364ebc1c9e8c3db371c2a5f73  NDO_JFm_Q03Absorb.olean
675c80b953343509a67d4136cb718c0313c5295308602baedc839a7e0361713f  NDO_JFm_Q03Reads.olean
93e0315d14e2741536bce425de2db4b24c4c3ef1675d2facadf0e8ea7f060844  NDO_JFm_Q04Absorb.olean
c76d130039cf16fc9d932dfe8f23772b5fa5afcc6c0703706a61b969e7d0b4a7  NDO_JFm_Q04Reads.olean
94da8c64838b9eebbe013566765510394aeabf094f326a4820c8c10201909678  NDO_JFm_Q05Absorb.olean
299ee90ddc0036300735683a6f0a5c9ac0e0244a7d2e28be0c3f098dd3a296ca  NDO_JFm_Q05Reads.olean
ae94f2709b0c3754d249ab3257a8f66f0a55736fd3eb98767452721a4d41f07d  NDO_JFm_Q06Absorb.olean
6b38347c48cf138f8e96743e5fb964aee01f8659d377f931a72dc0dbe022bcab  NDO_JFm_Q06Reads.olean
3ad13a9c014855f5a519819c061616d2e04d091a1dbd53daa1ba0e69d850f73e  NDO_JFm_Q07Absorb.olean
f808e238bf1ce72f77b487211d8f4e331503f09a90c3c5cd146beda9cfd44a44  NDO_JFm_Q07Reads.olean
e4a70f2f50d698b368ace2e745170f03272f7364cfb635a098bf4eb6a62e3e9c  NDO_JFm_Q08Absorb.olean
bd6c7fe84534afe1bb4163ee3f1c5bb35828455184d9bb899048aa1c2a95df8b  NDO_JFm_Q08Reads.olean
193d95470d74aa80c7e036e8bb235dae991bf3a02c6c5a78d6760f92de0408ed  NDO_JFm_Q09Absorb.olean
2a7a00d072002e4b33c8d21d580c0d9f3c27467bd932b3a88057ea406a8eda8a  NDO_JFm_Q09Reads.olean
81a2a67efc7393c25713f62919b6a5f03823ff80ae40b71978b8f8e882af7861  NDO_JFm_Q10Absorb.olean
03abcd9b6c80b5fdc5bb68e79bbd4e72b76566e7eabdabd7eb8e17d64d11747e  NDO_JFm_Q10Reads.olean
82f44614c8481621dc4202b3d2ce6426afd30ecbe937d40bea9926556d63d952  NDO_JFm_Q11Absorb.olean
317d0dc0bd8bc3027af443d66db9a60592406df8e016b1f14e0b120bea43c2b5  NDO_JFm_Q11Reads.olean
3ae391455abe1f1db0451c1a1632de18a4bb1f0a964ab27f01498c1ab940eefa  NDO_JFm_Q12Absorb.olean
1f076657815cdb584419eee376398d17bc8c8ae2606b3158664d95bab7eab3d4  NDO_JFm_Q12Reads.olean
5f51c46e4dd570e28c51738241ca21a773db6d9ab31e11c3b7d6d00e5dfafd19  NDO_JFm_Q13Absorb.olean
6e77037c70b96483ddd198e011cd7838d8a21a37c7de2559ab1d85537f545b18  NDO_JFm_Q13Reads.olean
de1ac8ddd0d625cd71bae8cd27d5b861ef7247b5c1e822e411264b8baf0e70c6  NDO_JFm_Q14Absorb.olean
4d2b4dbae2836c3d41a2af52fbb589c887f54db835aa5fc29cf1b4b28092fbb5  NDO_JFm_Q14Reads.olean
26bba710869a9774e8bd6a2d8e1229a0f1faee941268a69551cfdfdf7223515a  NDO_JFm_Q15Hashes.olean
bb8ecdd2c43e25492c6db02c461fdff69dc5348368309568e506404a9f2df9f6  NDO_JFm_Q16Hashes.olean
f2e58a248fd86fa910126c1abfa78d4d66c3d53f1bf04c8e645203424c436a43  NDO_JFm_Q17Hashes.olean
9c018146230275195523300d2c1f95b573cdce7acaf0822d210f5541a1d91f82  NDO_JFm_Q18Hashes.olean
6f1f1a0ca659237a504594fe9cf503f17d3ddb790e28859f98d47b88480efce5  NDO_JFm_Q19Hashes.olean
2217287fecff7949c05d5f7afaac8ad4c3839f2f0655d90fdc9bfd2a70e52a65  NDO_JFm_Q20Hashes.olean
0aca2081bf762f3784277b4d5288f51f35ef44007255dc3036062d8522f73edc  NDO_JFm_Q21Hashes.olean
23c2f0e27866cbbbc9494072a026549132f14da9c5744104c431abdc183c16e5  NDO_JFm_Q22Hashes.olean
321daf18e1f2293e7a3458c5eb495538d8083be030e71412c5f0e06c2873dacc  NDO_JFm_Q23Hashes.olean
16dbab8c482a90a30fd62527312ea7549843f4362573b33bf8ea63f6e4b3dcc4  NDO_JFm_Q24Hashes.olean
253a890b9b52c37b60628606b6ce5026a77e2942e23971168485496d25b48f0b  NDO_JFp_Query00Absorb.olean
299fd3537c9108844e8d7505f93479cd8e9c187d906a528a5dde53cedc1e8fc5  NDO_JFp_Query00Ratchet.olean
dfd3a86c8b8ae0612db6e55e27ede4996342ded03882b9e0e2b1461b3a5bea17  NDO_JFp_Query00Read.olean
baf076968702f85418303b02658e597f5dbca066a79f51e09ef0cf00d178e6b6  NDO_JFr_Boundary00.olean
3b5c4db4a4f0e6449b411352b3e7d9af35560e4601ce107e79676f01abfacee5  NDO_JFr_Boundary01.olean
65d8217d942167e977ee83f0502b82b59e576388a614ee9dfbd3c2e9f2356bc8  NDO_JFr_Boundary02.olean
ddd6082af863a84f31cf290a65941a8a522a18a85b52121c47bf2435d3770231  NDO_JFr_Boundary03.olean
88c260a0257d7cbff04a6e47b4d64a4670878df97d635a7e545a4eb1d8fbf7be  NDO_JFr_Boundary04.olean
f7efe02023e07fd665fa1d70786935822a11871545b1828ad418b82c4e2dc883  NDO_JFr_Boundary05.olean
56986bb195d0b4bc437dcf03be9212ceefec6c8bb7e4f0e57380c02deab118ef  NDO_JFr_Boundary06.olean
2aa45de2999982141f8b7a6da557d71da2a1791ce279bf7490bcb3d6850d5f62  NDO_JFr_Boundary07.olean
d39c19035b12875db94ec265174b8605a70087643fc4e8c9a188d33103d46257  NDO_JFr_Boundary08.olean
b32501c4c426d78fbac6b64a55dc1f8df8f24df02aa6ae469c58b57aa2a49d28  NDO_JFr_Boundary09.olean
ce4eba064fc3386a190a00b7e123168d2c08d2c0f67f9137c635400470d482b0  NDO_JFr_Data00.olean
7c8fd421183cd012b624d299dda9b4994ba6549a6119da5616bd9994f288873f  NDO_JFr_Data01.olean
7690c3d093a79ea0da148d02993793add9ddea024573315d1d682925c67062be  NDO_JFr_Data02.olean
fb32b08f355372cbd393939f8ce82fa4379df4470b0195c0f8e09f68d8f63aa2  NDO_JFr_Data03.olean
480b9ebc7e832ca626476568ccc6cdd8ae281983d49871bc48b13acbd6e032fa  NDO_JFr_Data04.olean
9b7b2a9880e9a2c16e2f7f49b6052ce8ded03a310cdb21623af6c2bfb3b64f86  NDO_JFr_Data05.olean
62b9b8dd819b512de27d2f894af98b04dcafb6e98b447e5f1208f554d2dfc4bc  NDO_JFr_Data06.olean
df87cb7f28d138f83963ea0fc8522fde78913bb83f62160e6605693aea44e557  NDO_JFr_Data07.olean
2b43c738f29dd84fa9321f3d5b81f7e573be6ed5ac9d22ae1ce406987dd3ac84  NDO_JFr_Data08.olean
ade46e9f3bdab9b48f915e230408bdcdf219b0abb6bee1bb9797cbdfc390856d  NDO_JFr_Data09.olean
9512b9f0aa94ba145f7774ce9714eec2db560cc45880a2a7041cd8bab2a3afcb  NDO_JFr_Horner00_0.olean
bdde7d1513cb93c18f7ebbefad468eb5e567f27d357e239282f7b5bb1430e93a  NDO_JFr_Horner00_1.olean
f09776d7642d138322a952253b34d94be6315139f6cfc446e62f8d130c5df26b  NDO_JFr_Horner01_0.olean
51283a9530882d41f5f34a183bce6a598f3595b4354e982f0c049e3f9da0a4aa  NDO_JFr_Horner01_1.olean
c51a8ce806e56465dd90b44f07a31560967e97f134a9641411466cd6e50b73d1  NDO_JFr_Horner02_0.olean
2296b5a6a388f3f228479640e4d3c5db5ccc265e6918368a2a46623d36df0db9  NDO_JFr_Horner02_1.olean
fe1c49122dc61413ada85808813da9e0afe60dadf48bb9400875756fa89190b2  NDO_JFr_Horner03_0.olean
e72c35e823585dbc9d7db0bdde2e1ffe18e63f90c57303723e73f63fb12ed7d4  NDO_JFr_Horner03_1.olean
fef30fde742bb1c79940a34d57a1d8053fcde2f488ae9b8290fbd8ad79eebb99  NDO_JFr_Horner04_0.olean
75a6e8e85bdcd1daeb7a7786e7181128c12e59b0d11721138ee5f34a1c93d763  NDO_JFr_Horner04_1.olean
d34dcb268731c40b9c922642cd2cf2c4acd7c9bafd87f6308c4d24e2c65ba3ae  NDO_JFr_Horner05_0.olean
8c4dd1676da4743e8991f8466beb73b0b05433efc9d5837be77541e4e2715cba  NDO_JFr_Horner05_1.olean
f74a21df4b09082a847baaa5a618465d3aba4e6f92c73c8bf01c2221e7ea2a6a  NDO_JFr_Horner06_0.olean
9d3b12bcb8537510749433e6d811ae7bdc505f25267b4525d77ca9b756a51416  NDO_JFr_Horner06_1.olean
302eafe8d720a3dcb4804eca8197ee0f368ae3bb39a5a38085491de5ea842391  NDO_JFr_Horner07_0.olean
2bdbed7e4f0262b7ea5a92c3055c47dff428a63fad89f50681fd4ef2038a0379  NDO_JFr_Horner07_1.olean
51b5331e1e82404d1421f00253ccfd658848baf3f6362b65d722b77307792667  NDO_JFr_Horner08_0.olean
4781cae6af2fbfca20634831289a0e1ba490942ab016fbe9d613e331824a4299  NDO_JFr_Horner08_1.olean
06da7346fabae7d28e364e3acb0da6ae3ffe736ae6eee7f62bb6f63f94c2f472  NDO_JFr_Horner09_0.olean
a314246dbc8459d41d6564cae704618737873c1e7ea6cc08cc01eb421b8cb1cd  NDO_JFr_Horner09_1.olean
dba425f9ccd9f9bcf6e4a598cd1941627d17a894302b3659dc0d363db9128291  NDO_JFr_HornerTrace.olean
31328ad57453f5310e734a8f4b91ef446825fa3e338571cd0b8a59507c00ab5c  NDO_JFu_Q25Aggregate.olean
88a4347a476aa6c43d8a7c1bcc90431577950c7c72ff94cf903499057eed4dfe  NDO_JFu_Q25Block00.olean
589cf77290369bc193220aff58c59064ad9705b94afd947f64dfc393bdfde39a  NDO_JFu_Q25Reads.olean
fb32a6f66bf2890e0dc73249e0fbf7ea6986dcb26a0b3d0529628456797cdc77  NDO_JFu_Q25Window01.olean
514a02ab809d18dc5a05b53e83e55b2f328dc80ea7979fd6f044f2cd622ed851  NDO_JFu_Q25Window09.olean
ea11c036dca71acaafc74e80e8b2311f6825f00222e30d0fc59ddbe263ab7ac0  NDO_JFu_Q25Window17.olean
e800e415d13e8802caefe7bae3f1f2b16a5f6f61717eebccbf2509808d1998cb  NDO_JFu_Q25Window25.olean
da89fabe0174d9b445f6be75301426806cc6ef82e0c7d1eaee97a53933e1baea  NDO_JFu_Q25Window33.olean
5ba23c2e095bcae254ec00536fd22feca0f2f159123a0f3a7901b1e98429da1c  NDO_JFu_Q25Window41.olean
05054c8e7403549dfd81e078392ccc70e021ae2d5bc3299c24d7891e118ecadd  NDO_JFu_Q25Window49.olean
416c3392965ea0241f9dbad0edf47067cb95e4ae7ecae70d90447801ec5a5688  NDO_JFu_Q25Window57.olean
620b1b79ba4e3bc72c72e1cda4951a2ce2f78a379f39499ae51fd2af4bf37698  NDO_JFu_Q26Aggregate.olean
fa27f981826f834d76e532d58d80c869e67ef82fc9f64ecc6a19cfaa30e76785  NDO_JFu_Q26Reads.olean
840361ad5b4981cfeedb2076c7eded38520ee20acf7d34d13acf8247dc22e75d  NDO_JFu_Q26Window00.olean
e1f5d8880aacda29ef05a3fae1f4643c983caf39e1575dcae98c2e2a79cc49d0  NDO_JFu_Q26Window08.olean
```

## 8. Remaining obligations and next deliverable

- W3c's `PIN2_NEWGATE_r0` import clash has to be fixed. W4's statement-layer restatements then compile (seed `JFr_SeedBoundary`, `JFp_SHADigest`, `JFw_Frames`/`NativeRow*`). After that, `NDO_JFm_Q01..24Source`, `JFu_Claims*` and `JFu_Q25InputBase` are next, and their sources are already generated here.
- The remaining in-closure transcript consumers (`JFy`, `JFv`, the non-JF `NKI_InitialPrefix` etc.) still need the same check-then-substitute treatment against `PIN2W5_VALUES.json`.
- The TX2 families outside the closure need the same treatment if they are wanted.

This job produced the native values and a format proven against the October fixture. It closes no premise of the security statement.

## 9. Files

- `inputs/` (with `SHA256SUMS`), `tooling/` (dumper source copy)
- `PIN2W5_DUMP.txt`, `dump.stderr`, `PIN2W5_dump.py`, `PIN2W5_derive.py`, `PIN2W5_VALUES.json`
- `PIN2W5_crosscheck.py`, `CROSSCHECK.json`
- `provenance-26oct/` (4bb3b3f dump, derived values, `PROVENANCE.json`, manifest diff), `PIN2W5_provenance.py`, `PIN2W5_hardcoded.py`, `HARDCODED.json`
- `PIN2W5_regen.py`, `PIN2W5_split25.py`, `REGEN-check.json`, `REGEN-pin2.json`, `sources/` (179), `generated/`, `PIN2W5_shape.py`, `SHAPE.json`
- `PIN2W5_ready.py`, `PLAN.json`, `PIN2W5_blocked.py`, `BLOCKED.json`, `PIN2W5_compile.sh`, `PIN2W5_drive.py`, `drive_status.tsv`, `drive.log`, `logs/`
- `OVERLAY-PIN2-W4.before.sha256`, `OVERLAY-PIN2-W4.after.sha256`, `HASHES.txt`, `SHA256SUMS`

target not yet established
