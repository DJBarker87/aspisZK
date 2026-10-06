# Wide-field port log

Historical status (2026-10-05): **Phases 1–4 complete.** Both agreement theorems are proved generically and at WideExact; the QM31 regressions reproduce the original V7 statements. All endpoint audits contain only propext, Classical.choice and Quot.sound (or a subset).
Finishing at the requested Phase 4 checkpoint. **Phase 5 was not started:** the matched degree-three bound, joint-list bound and subfield-descent lemma remain unproved by this port. The R0 paper argument remains unreviewed; this port does not establish its complete 100-bit soundness claim. The V8 round loop remains paused.

## Completed results

- Generic hypotheses: `{K : Type} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K]`. No extra field-cardinality or characteristic premise is assumed.
- `AspisWide.Terminal.exactV7InitialWidth29CurveDecodable`: `Width29CurveDecodable exactInitialEncoder 38229 initialBatchChallengeCap`.
- `AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable`: `DegreeThreeCurveDecodable exactFinalEncoder 9557 foldChallengeCap`.
- `Wide/Instances.lean` instantiates both at `AspisWideTower.WideExact` and proves the literal caps remain `336869026605739` and `9396508281246`. The unchanged `WideTower.lean` independently checks `Fintype.card WideExact = P ^ 8`.
- `Wide/EncoderRegression.lean` proves both encoder equalities at QM31 by `rfl`. `Wide/Regression.lean` derives the original V7 statements from the generic port through those equalities, then checks equality with the original proof terms by proof irrelevance.
- Final source audit: all 47 new Lean files match their recorded SHA-256 and an exit-0 compile, with 298 P/C/Q-only axiom reports. WideTower has five additional clean reports. The generic import closure has 75 project modules: 44 new generic modules and 31 unchanged cached modules; none of those cached modules mentions QM31Exact or CM31Exact. The two regression files and wide-field instantiation are outside that generic closure.
- No frozen V7 source, crate, program, other research directory or existing WideTower source was changed. No sorry, axiom or native_decide occurs in the new Lean sources. No heartbeat limit was raised to resolve a failure; inherited settings are recorded per target. New final reconstruction helpers use local 300000-heartbeat settings, and the cardinality helper uses the default.
- Only final Lean sources under `lean/Wide/` and this log are included in the commit. Scratch sources, commands, raw logs and compiled objects remain outside the repository.

## Scope and environment

- Sources: `research/v8-wide-reference-20261005`, base `9416a8c93fc269f6d3590002f5e6948fa17fb14a`; each row records the exact source SHA-256 compiled on that base.
- Read-only cached workspace: `/Users/dominic/ZK/AspisFormal`, checkout revision `acd4c0f0d0049d42c9fcb9525900fbb8932f1baf`, Lean 4.32.0, existing September 13 objects. No `lake build`.
- NUC Lean commit: `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`. The toolchain and lake manifest match the baseline.
- Objects and raw evidence: `/tmp/aspis-wide-port-20261005/`; nothing there is committed.
- One Lean job at a time, `-j1 -M4500`. Attempts 001–028: Mac, `/usr/bin/time -l`, descendant RSS stop threshold 7.5 GiB. Attempts 029 onward: NUC, GNU `/usr/bin/time -v`, one systemd scope per target, fixed Lean -M4500 and MemoryMax=7G, MemorySwapMax=0, ten-minute timeout for the required review point.
- Migration followed the user’s request to use the NUC. NUC workspace `/home/dombarker/project-offloads/aspis-wide-port-20261005`; read-only mathlib cache from `ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal`. Lean toolchain and lake-manifest.json match the task baseline. All 267 baseline project objects were copied unchanged and SHA-256 verified in an external overlay, taking precedence over the older NUC project cache. Previously successful new objects were also copied; no frozen dependencies were rebuilt.
- NUC preflight: no active Aspis build scopes; active finite cgroup caps 44.375 GiB, plus this scope 7 GiB = 51.375 GiB, below the host policy limit 55 GiB. Approximately 50 GB memory available at inspection. No other services were stopped or changed.
- Generic encoder imports have 29 cached Aspis dependencies; the complete generic agreement closure has 31. None mentions QM31Exact or CM31Exact. Only the two separate regression modules import V7 transcript context.
- Scoping correction: absence of a field name does not imply import independence. Ten additional helper modules require copies with redirected imports: Interpolation, Hensel, LocalFactors, RegularWeights, RegularRing, RegularZeroCount, HenselCombinatorics, RegularEvaluation, FactorBudgets, AmbientCurve. The requested Initial wrapper is also syntactically field-agnostic.
- All 40 inspected original encoder/list/agreement source files match the main checkout byte for byte.
- Field facts: odd characteristic and nonzero small natural casts follow from the injective M31 algebra map. Smooth needs only 223 * 114687 < card K; this follows already from P ≤ card K, so no assumed cardinality or weakened degree bound is introduced.

## Exact command

Run from `/Users/dominic/ZK/AspisFormal`, with `root` the research `lean/` directory and `outdir=/tmp/aspis-wide-port-20261005/objects`:

```sh
/usr/bin/time -l lake env sh -c 'export LEAN_PATH="$LEAN_PATH:$1"; exec lean -j1 -M4500 -R "$2" -o "$3" "$4"' wide-compile "$outdir" "$root" "$outdir/<Module>.olean" "$root/<Module>.lean"
```

## NUC command

Each target runs in its own `systemd-run --user --scope` with `MemoryHigh=3G` (from 053; 050–052 used 1280M, 033–049 used 1G, earlier probes 5G), `MemoryMax=7G`, `MemorySwapMax=0`. One job at a time, with reservation checks before each launch. GNU time uses `-v` on Linux (`-l` is the Mac interface).

From 058 onward, inside that scope and the pinned NUC Lean workspace, the command is:

```sh
lake env python3 "$task/evidence/compiler_env.py" capture "$task/evidence/environment-$attempt.json"
/usr/bin/time -v -o "$task/evidence/time-$attempt.log" timeout 600 stdbuf -oL -eL python3 "$task/evidence/compiler_env.py" exec "$task/evidence/environment-$attempt.json" "$cache_view" "$task/pinned-cache" "$task/objects" "$task/sources" "$task/objects/<Module>.olean" "$task/sources/<Module>.lean"
```

The external helper captures only Lake compiler paths/options in a mode-600 file (ELAN, ELAN_HOME, ELAN_TOOLCHAIN, LAKE, LAKE_HOME, LEAN, LEAN_SYSROOT, LEAN_AR, LEAN_CC, LEAN_PATH, LEAN_SRC_PATH, LEAN_GITHASH, PATH, LD_LIBRARY_PATH). Lake exits before Lean starts. The helper restores those variables, prefixes the unchanged cache view and pinned overlay to LEAN_PATH, appends the new object directory, and executes `$LEAN -j1 -M4500 -DElab.async=false -R "$root" -o "$out" "$source"`. No credentials are captured.

Earlier NUC commands kept Lake as the parent through 045; 046–057 resolved LEAN_PATH before Lean, with synchronous elaboration from 048. The per-attempt raw evidence retains exact commands. Cache preparation and cleanup are outside timed Lean wall time. The scope records effective limits, memory peak, swap peak and OOM events. Sources, object cache and raw evidence remain outside the repository.

## Resource observation

Resolved cardinality instance mismatch (075–076): fully explicit inspection shows that concrete Fin 262144 selects SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat, while a symbolic Fin n selects Fin.fintype. Comparing their enumerations caused the large reduction. The final Wide.Cardinality lemmas quantify over any Fintype (Fin n) and use Fintype.card_congr (Equiv.refl _) to compare cardinalities symbolically. Both lemmas compile in 1.22 seconds with only P/C/Q. The concrete full-import probe (077) then passes, and FinalCurveBranch (078) compiles in 40.84 seconds at 4,071,653,376 bytes RSS with zero swaps and P/C/Q only. This is an enumeration-independent theorem, not an added assumption about the encoder or field.

Cardinality review (066–067): after splitting the final proof, the remaining growth occurs in selected-branch cardinality packaging. The replacement proves card_fin_lt_of_budget with symbolic domainSize and curveDegree, then applies that opaque theorem at the concrete domain sizes. The helper compiles in 1.20 seconds, peak RSS 1,554,071,552 bytes, zero swaps, P/C/Q only. Both final and initial wrappers use it; no domain, reserve, threshold, or cap changes.

Terminal proof-shape review (058–063): incomplete prefixes elaborate promptly through final reconstruction, but are explicitly not proof evidence. Direct Nat inequalities replace the final broad omega call. The remaining full-declaration growth is addressed by splitting final specialization, branch lift, selector, curve extraction, and terminal packaging into opaque declarations, following the existing V7 initial-proof structure. The first helper (063) compiles with a clean audit, unchanged hard caps and zero swaps. No statement, threshold, or cap is weakened.

Full-cache layout review (051–053): the private-only view left shared public Mathlib pages outside the active cgroup and too little reclaimable space for the proof heap. The replacement copies every Mathlib .olean/.olean.private/.olean.server/.ir artifact unchanged into the per-scope view. MemoryHigh=3G remains below the original 5G soft threshold; the hard limits -M4500 and MemoryMax=7G remain fixed. Minimal import probe 053 passes at 3,887,112,192 bytes RSS with no swaps. No object contents or proof premises were changed by this cache-layout correction.

Terminal resource review (045–050): the 1G MemoryHigh working threshold was below the observed live working set, causing sustained reclamation throttling. Lake was changed to finish environment resolution before Lean starts (046 onward); the broad specialization simp was replaced by a named rewrite (047 onward); synchronous elaboration was selected with -DElab.async=false (048 onward). After a flushed-checkpoint diagnostic also stalled, the soft reclamation threshold was set to 1280M, below the original 5G threshold. The hard caps -M4500 and MemoryMax=7G and MemorySwapMax=0 were never raised. Minimal import probe 050 passed at 4,163,375,104 bytes peak RSS. Attempts 045 and 046 were stopped by terminating the scope, so their timed peak and swaps were not captured; subsequent stops terminate only Lean to preserve time statistics.

After attempt 039, the preflight for FixedBranchCurve stopped before launching Lean (exit 78): active finite cgroup caps rose to 60.375 GiB, so adding 7 GiB would exceed the NUC policy limit of 55 GiB. Two unrelated 16 GiB crypto-tax borrow containers were active. No other service was changed. The diagnostic container then exited; the sequence resumed at FixedBranchCurve after a fresh successful reservation check. This was a resource reservation hold, not a failed Lean elaboration.

NUC attempts 029–031 failed at the fixed Lean memory limit during import, including a bare Mathlib import probe. A module-mode probe (032) succeeded but cannot import the unchanged legacy V7 modules. Attempt 033 solved the import footprint without raising a cap: copy the unchanged Mathlib private object segments into a fresh per-scope cache view; symlink its other artifacts unchanged; prepend that view; lower MemoryHigh to 1G. This charges the private file pages to the active scope so Linux can reclaim them. The proof environment, serialized objects, Lean -M4500, MemoryMax=7G and no-swap policy remain unchanged. The scratch probes are recorded below and are not final port sources. Cache preparation and cleanup occur outside the timed Lean command; total scope wall time is retained in raw evidence.

During RegularEvaluation, the host had roughly 11 GB in the macOS memory compressor. That target completed in 385.14 seconds with peak RSS 2,677,932,032 bytes, a clean audit, and zero swaps reported by the timed job. The low CPU-to-wall-time ratio was consistent with host contention; neither proof limits nor memory caps were raised.

## Compile records

Final source paths below are relative to `docs/research/v8-wide-reference-20261005/lean/`. Nuc-prefixed diagnostics instead live under `/tmp/aspis-wide-port-20261005/probes/` and are not committed.
RSS is the timed process peak in bytes; swaps are reported by the platform time utility. Attempts 029 onward also enforce zero cgroup swap.
P/C/Q means only `propext`, `Classical.choice`, `Quot.sound` (or a subset).

| Attempt / target | SHA-256 | Exit | Wall seconds | Peak RSS bytes | Swaps | Source revision | Axiom audit | Heartbeats |
|---|---|---:|---:|---:|---:|---|---|---|
| 001 `Wide/InitialEncoder.lean` | `5008b8fa5eb6439b7b1af51cbeded5aea596262b4d8c90eec6cbbffe57bb2b46` | 1 | 83.01 | 3297624064 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 002 `Wide/InitialEncoder.lean` | `518bf5e70161f11981f3c0b97f95f88efe08e0d3065d54848079e507138552b2` | 0 | 82.83 | 3323412480 | 0 | `9416a8c93` + source SHA | 4 reports, P/C/Q only | default (200000) |
| 003 `Wide/FinalEncoder.lean` | `6ae59a2d5f9d2d5d56b70ac6c67121d3bcb26f42470bafb3e2d798429590488f` | 0 | 83.14 | 3400318976 | 0 | `9416a8c93` + source SHA | 4 reports, P/C/Q only | default (200000) |
| 004 `Wide/GRSConversion.lean` | `5bbe34464895219081066afcfa49a81b258af878b12d9e73f8b93868f70051c7` | 1 | 72.86 | 3694379008 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 005 `Wide/GRSConversion.lean` | `436175dcfcfe45303aa20f20f9fae078b36ba6aa117f6b58c08aa8197bf755ba` | 1 | 118.69 | 3465379840 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 006 `Wide/GRSConversion.lean` | `dd467110bbaf387421f099a90ed87e1259ff8a169933245f8def0ca57eb3fbfb` | 1 | 122.0 | 3368402944 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 007 `Wide/GRSConversion.lean` | `df621ca75572edf4e5291d1c64b802a158303e404a5b7f0ec3e63630acd39255` | 0 | 125.69 | 2827812864 | 0 | `9416a8c93` + source SHA | 16 reports, P/C/Q only | default (200000) |
| 008 `Wide/EncoderLinearity.lean` | `14fab916cb20666ee40cf6e62281c4282cfd36c23af38fca4042dce249c8ee5f` | 0 | 93.02 | 3217555456 | 0 | `9416a8c93` + source SHA | 4 reports, P/C/Q only | default (200000) |
| 009 `Wide/ReleasedLift.lean` | `fd04f0b241ee320b200be7340f97017982adba2fa1bb59131b621adc704d555d` | 0 | 90.25 | 3067969536 | 0 | `9416a8c93` + source SHA | 4 reports, P/C/Q only | default (200000) |
| 010 `Wide/EncoderRegression.lean` | `4535cbb3a56a47bbec7f95175fa30c4ccf69e5788018bc5b505119283e832d48` | 0 | 83.29 | 3248422912 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | default (200000) |
| 011 `Wide/MultiplicityThreeGS.lean` | `73252b85be6db2b7a0180d9f942e1872a75a57e6257dfb36124139bb27f277b5` | 0 | 94.22 | 3363274752 | 0 | `9416a8c93` + source SHA | 19 reports, P/C/Q only | 800000 local, 800000 local |
| 012 `Wide/Interpolation.lean` | `834bdc8c5b3d16c42d25e55d9be9895e2d6ed2a035c949487369667bbe3dec4a` | 0 | 78.15 | 4061462528 | 0 | `9416a8c93` + source SHA | 8 reports, P/C/Q only | default (200000) |
| 013 `Wide/Factors.lean` | `44cbdc81be8d8aa519c170fbd511dc4cd70885bfe0a1762f7e3de97d82e647f7` | 0 | 68.41 | 3784491008 | 0 | `9416a8c93` + source SHA | 10 reports, P/C/Q only | default (200000) |
| 014 `Wide/Agreement.lean` | `783b14e3f958071f52a7dafe8d4bb76a4360e7a49e4de3a22f87eda2023b0338` | 0 | 60.02 | 3926081536 | 0 | `9416a8c93` + source SHA | 8 reports, P/C/Q only | 1000000 local, 1000000 local |
| 015 `Wide/Smooth.lean` | `236ddbdc270bc67d62b1deea5d5a1ce01cdd8884584fc54c9a002c783735dc7e` | 0 | 72.61 | 3589963776 | 0 | `9416a8c93` + source SHA | 10 reports, P/C/Q only | 1000000 local |
| 016 `Wide/Hensel.lean` | `92342560420c536f7b622c2c0031d4a233c545af82e1392409446bf7ed8ff890` | 0 | 68.26 | 3836772352 | 0 | `9416a8c93` + source SHA | 5 reports, P/C/Q only | default (200000) |
| 017 `Wide/LocalFactors.lean` | `d6225243413d8ac80843063d3f1d99468f6a51a852083ce8a980de1a3252fdb7` | 0 | 66.96 | 3966205952 | 0 | `9416a8c93` + source SHA | 7 reports, P/C/Q only | default (200000) |
| 018 `Wide/FunctionField.lean` | `c4bfa3d14cbf56ca5686be890a375746e6711d57b029514cff81a1b5ab56a41c` | 0 | 74.61 | 3727949824 | 0 | `9416a8c93` + source SHA | 4 reports, P/C/Q only | default (200000) |
| 019 `Wide/PowerSeriesLift.lean` | `2932fdc22cdf579950bb29e8c822e0c1e23f56bcb1c0e99b336928874e874c93` | 0 | 81.94 | 3774529536 | 0 | `9416a8c93` + source SHA | 3 reports, P/C/Q only | default (200000) |
| 020 `Wide/RegularWeights.lean` | `7b583549cc3d32cb23c569ab4643243449e0fd0567694284452944e4c2660b6e` | 0 | 80.12 | 3625484288 | 0 | `9416a8c93` + source SHA | 15 reports, P/C/Q only | 1000000 local |
| 021 `Wide/RegularRing.lean` | `51023907cbdb8889f21187fc6cbf0bede997bc01eb9ac65f4f1c637a91cb9310` | 0 | 145.88 | 3194781696 | 0 | `9416a8c93` + source SHA | 18 reports, P/C/Q only | default (200000) |
| 022 `Wide/RegularZeroCount.lean` | `32ea002db6bebd19d3628efd91f974bf8a95bcdff2bd91637ac1341472478912` | 0 | 173.88 | 3464822784 | 0 | `9416a8c93` + source SHA | 8 reports, P/C/Q only | default (200000) |
| 023 `Wide/HenselCombinatorics.lean` | `b0171895d4a4a6acaaf06e92d5360457e4ac55e905616eb55482750b04c3f001` | 0 | 178.7 | 2693611520 | 0 | `9416a8c93` + source SHA | 16 reports, P/C/Q only | default (200000) |
| 024 `Wide/RegularEvaluation.lean` | `a116ef5450c482aa291df40e008840305ffde91d856b3b8bce3d34aef8ee874d` | 0 | 385.14 | 2677932032 | 0 | `9416a8c93` + source SHA | 5 reports, P/C/Q only | default (200000) |
| 025 `Wide/RegularHensel.lean` | `e2c4af177e5e802d43c4d81db90b182002bfcd6850ae344314382202dc0f661d` | 0 | 77.01 | 3385327616 | 0 | `9416a8c93` + source SHA | 5 reports, P/C/Q only | default (200000) |
| 026 `Wide/HenselRecurrence.lean` | `46658b8d22df6786e1442da16470ddf8e49bb6d2fef4c6d9ae4396f4095fb148` | 0 | 78.19 | 3181346816 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 027 `Wide/FactorBudgets.lean` | `9703a2245522f18e90b29b84ab353c92630daa56487381db92f2d4fedb07d196` | 0 | 115.28 | 2462498816 | 0 | `9416a8c93` + source SHA | 16 reports, P/C/Q only | default (200000) |
| 028 `Wide/HenselWeights.lean` | `7047f79fd0e6c592161c728220fdd474ee5a68a446a1647ffb3ce3decf193d4a` | 1 | 111.28 | 2570338304 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 029 `Wide/HenselWeights.lean` | `7f95af03f66b47170eb3efa75bcc17e5a15b59977ee9b4b661c031466109ced8` | 134 | 21.44 | 5383118848 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 030 `NucImportProbe.lean` | `fb4853ca10c3cc38b7a870439bdcd6960558b77d04487f603d6d42e3284ab01f` | 134 | 6.83 | 5832695808 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 031 `NucMathlibProbe.lean` | `54b7f5b62e0ec6ad6ebca7b7ab2674a02f5c370736b1318b948e8a305e743a06` | 134 | 3.61 | 5862318080 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 032 `NucModuleProbe.lean` | `036c20201ae6091ecde46c8d163434051e5980832635e11777c959cd852b0440` | 0 | 3.63 | 3739770880 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 033 `NucMathlibProbe.lean` | `54b7f5b62e0ec6ad6ebca7b7ab2674a02f5c370736b1318b948e8a305e743a06` | 0 | 77.4 | 4028276736 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 034 `Wide/HenselWeights.lean` | `7f95af03f66b47170eb3efa75bcc17e5a15b59977ee9b4b661c031466109ced8` | 0 | 87.41 | 4057292800 | 0 | `9416a8c93` + source SHA | 21 reports, P/C/Q only | default (200000) |
| 035 `Wide/HenselIntegralLift.lean` | `ecd52be61f8c171a699e4ef69963aeb6a7a90b72416a8bf7b41f347780018a80` | 0 | 94.89 | 4091129856 | 0 | `9416a8c93` + source SHA | 15 reports, P/C/Q only | default (200000) |
| 036 `Wide/HenselSpecialization.lean` | `d7e48ffa237f8f31a0362986fb3b8b87afedbb49c33aa0460e12e700991a3b2f` | 0 | 82.7 | 4075921408 | 0 | `9416a8c93` + source SHA | 13 reports, P/C/Q only | 2000000 module |
| 037 `Wide/FiniteBranch.lean` | `cf72efcdc93a02a613250adde3c5ae29981005cd061aee801b5e1c19f6af28f0` | 0 | 85.23 | 4068155392 | 0 | `9416a8c93` + source SHA | 8 reports, P/C/Q only | default (200000) |
| 038 `Wide/BranchEvaluation.lean` | `d23b7e1579f449a5f2f538467f5ed06f443b65a2877152e6226f5b0e672f5f41` | 0 | 85.71 | 4083236864 | 0 | `9416a8c93` + source SHA | 11 reports, P/C/Q only | 2000000 module |
| 039 `Wide/AmbientCurve.lean` | `23d46d5d838ec039207e0da64fbf75f467e3d130ef387770df950a54826a17bc` | 0 | 78.8 | 4077084672 | 0 | `9416a8c93` + source SHA | 3 reports, P/C/Q only | default (200000) |
| 040 `Wide/FixedBranchCurve.lean` | `e5ae149712e4f251134954c68b24adee600e3454fda16e86670eab586c0ec0f7` | 1 | 183.75 | 3640610816 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 041 `Wide/FixedBranchCurve.lean` | `dfd6574eaa4a7777253b2ca7061d1661176d27998669c29365aea434f716ae53` | 0 | 97.57 | 3725295616 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 042 `Wide/ConcreteBranch.lean` | `e63db02d15d497071a0694f833bfca2a1c94be8e98d906db7ccd62a1c300664c` | 1 | 157.86 | 3894136832 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 2000000 local, 2000000 local |
| 043 `Wide/ConcreteBranch.lean` | `2af45f9a045e4d91a196d59957fb5728defe555469e2ec0ae6284b586204d1a9` | 0 | 88.33 | 3923705856 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 2000000 local, 2000000 local |
| 044 `Wide/OuterSelection.lean` | `ae6bd2a461611ab79ecc0c67bae571887cbef031505629e90bb4004e4ebc45b7` | 0 | 88.69 | 3950534656 | 0 | `9416a8c93` + source SHA | 5 reports, P/C/Q only | 2000000 local |
| 045 `Wide/Terminal.lean` | `33e832be64ec2ed093de4d342d05c32066891ace77980910154d9ede41dae4c0` | 255 | 446.11 | not captured | not captured (no swap enforced) | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 046 `Wide/Terminal.lean` | `33e832be64ec2ed093de4d342d05c32066891ace77980910154d9ede41dae4c0` | 255 | 312.11 | not captured | not captured (no swap enforced) | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 047 `Wide/Terminal.lean` | `625621953618b198cb658d5d0efd933b0924eb7b46de78463155be0c1bd45999` | 143 | 204.44 | 4263010304 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 048 `Wide/Terminal.lean` | `625621953618b198cb658d5d0efd933b0924eb7b46de78463155be0c1bd45999` | 143 | 189.73 | 4262375424 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 049 `NucTerminalProbe.lean` | `1ec505cfca712bc0e53631a20922a7abdac44a893ab22bb72ff93cbc17352f31` | 143 | 213.4 | 4282363904 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 050 `NucMathlibProbe.lean` | `54b7f5b62e0ec6ad6ebca7b7ab2674a02f5c370736b1318b948e8a305e743a06` | 0 | 61.16 | 4163375104 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 051 `Wide/Terminal.lean` | `625621953618b198cb658d5d0efd933b0924eb7b46de78463155be0c1bd45999` | 143 | 266.6 | 4602896384 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 052 `NucTerminalProbe.lean` | `5fbc600749db3e6cb597ab62fbaecb55eee0e87e8f0d4b96f19973990c56808d` | 143 | 181.38 | 4514959360 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 053 `NucMathlibProbe.lean` | `54b7f5b62e0ec6ad6ebca7b7ab2674a02f5c370736b1318b948e8a305e743a06` | 0 | 41.89 | 3887112192 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 054 `Wide/Terminal.lean` | `625621953618b198cb658d5d0efd933b0924eb7b46de78463155be0c1bd45999` | 143 | 353.35 | 4353196032 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 055 `NucTerminalHeader.lean` | `e501112129fcd3879f945554035f5048cd88b5399193ac079c9cdad83a4b2262` | 0 | 54.16 | 4042604544 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | default (200000) |
| 056 `NucTerminalProbe.lean` | `5fbc600749db3e6cb597ab62fbaecb55eee0e87e8f0d4b96f19973990c56808d` | 143 | 247.57 | 4352757760 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 057 `NucTerminalProbe.lean` | `608c66149943a3b07307f4751ee69a307506bc9f0f05d3e370bd1c62987e56af` | 143 | 384.33 | 4355936256 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 30000 local |
| 058 `NucTerminalPrefix.lean` | `fd6a5c13d22bb7697ae9897200a25b891a354b6491d6a22cd9da7d949a154889` | 1 | 40.31 | 3964915712 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 30000 local |
| 059 `NucTerminalPrefix.lean` | `a239c662b724da5e6915c8a377dee5e4d5d103871cc308fb98b4ef5257737c2c` | 1 | 40.13 | 3946201088 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 30000 local |
| 060 `NucTerminalPrefix.lean` | `46fa358d6024ea2313e89f9bf6f02cade9dd5ee38e8c80046d916fa115b14590` | 1 | 40.48 | 3958194176 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 30000 local |
| 061 `NucTerminalPrefix.lean` | `874364fed0419081ebc5798ac4558763c41436c26b6e568e08ede377df6d1e50` | 1 | 40.57 | 3982512128 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 30000 local |
| 062 `Wide/Terminal.lean` | `210ba436f45ade61dc7c2b776387f1b19fd537d0fb29be8b6d728b0f915b933e` | 143 | 82.89 | 4356071424 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 063 `Wide/FinalRoot.lean` | `aa8ad2e10b8c455cdbf9a08c11f0650aacf849fe66750bc7118f870fed988ad3` | 0 | 40.65 | 4085092352 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 300000 local |
| 064 `Wide/FinalBranch.lean` | `38bfe106ddfc3c9fff5893d48aa31236022bbdfe0e80951a4880a8e9b16e86e5` | 0 | 41.24 | 4065968128 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | 300000 local |
| 065 `Wide/FinalSelection.lean` | `f54b193d353e0f706a98d88fbcb3b059cb9713bc40ac54df8111117988ba8ec9` | 0 | 42.21 | 4028743680 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | 300000 local |
| 066 `Wide/FinalCurveBranch.lean` | `b84dbacce50f16a86466ccc43c76a23427262198e31ddfac9666da2f0722c964` | 143 | 97.79 | 4347244544 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 067 `Wide/Cardinality.lean` | `473b15c39c292873615911b1d4ba2afe97b714a615e5655dc288e67a6f288326` | 0 | 1.2 | 1554071552 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 068 `Wide/FinalCurveBranch.lean` | `a932e51ab53203f327606ad1db0259044d586de5095e28d8e260dc08758c3651` | 1 | 55.7 | 4219117568 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 069 `NucCardinalityApply.lean` | `f94b001d881b29322c5b8e54f6c2332345c73718d4f405f425572b382fda039d` | 1 | 1.13 | 1544724480 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 070 `NucCardinalityApply.lean` | `05a982df4d83eda48e94895a033ba3f9e995a3fc43241fd8ee0751463b63f928` | 0 | 1.08 | 1550741504 | 0 | `9416a8c93` + source SHA | diagnostic passed; no target audit | default (200000) |
| 071 `Wide/FinalCurveBranch.lean` | `27fc6fc66a96534662506fc17171936cada63ab2c0dc4e1f031a6e4e966733fa` | 143 | 93.44 | 4350726144 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | 300000 local |
| 072 `NucCardinalityApply.lean` | `7747cf8efe876c2208337e08c24117816e4921a753a25976467968a4f7156472` | 143 | 82.95 | 4344832000 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 073 `Wide/Cardinality.lean` | `0876e792e404e8240f97d87dfb08136d0e4a97dfca006552106a25de4e919df1` | 0 | 41.11 | 4026601472 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 074 `NucCardinalityApply.lean` | `e20a5d0cee2e0206baf3c50ed373fa37b6bec283a8f810344506f26b127b6cd2` | 143 | 96.14 | 4345606144 | 0 | `9416a8c93` + source SHA | FAILED; no proof claim | default (200000) |
| 075 `NucCardinalityInspect.lean` | `e2af9cb5955aee2104e164bfafd6998ca5986a4195c2e7dde97643f571a6448a` | 0 | 42.69 | 3948830720 | 0 | `9416a8c93` + source SHA | diagnostic passed; no target audit | default (200000) |
| 076 `Wide/Cardinality.lean` | `373ba7d10692b6ddad737919145cc3b1c2672ff22716ae7ff664939740b82fb9` | 0 | 1.22 | 1555103744 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | default (200000) |
| 077 `NucCardinalityApply.lean` | `7453d58d2447701966889297eab8c77055e85fc78c166fa3b01d2c6e083f57e6` | 0 | 41.56 | 4064620544 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | default (200000) |
| 078 `Wide/FinalCurveBranch.lean` | `27fc6fc66a96534662506fc17171936cada63ab2c0dc4e1f031a6e4e966733fa` | 0 | 40.84 | 4071653376 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | 300000 local |
| 079 `Wide/FinalCurve.lean` | `a65691e03f23e30147f549c86f954c8046192f182b27d1acd1b4aa2c181ef416` | 0 | 41.63 | 4060033024 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 300000 local, 300000 local |
| 080 `Wide/Terminal.lean` | `943d9b78b162fe3f60709309db5bd28ec9acd99088f90eb6203ea49bb26b0daf` | 0 | 41.26 | 4056866816 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 300000 local |
| 081 `Wide/InitialRoot.lean` | `2c0c645d5892f2d34f4162ff8b97caa6da39956e7d68cc09e5244eb3bbe06adf` | 0 | 41.24 | 4071968768 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 2000000 local |
| 082 `Wide/InitialBranch.lean` | `c01ee2940d3149a9c7353625e23e2dd9039957360c809b1e7f5434c5aa09f81e` | 0 | 43.19 | 4059693056 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | 1000000 local |
| 083 `Wide/InitialSelection.lean` | `1c1cadb34447617d5927c4146c8368d924741c63b1544abdb88f82398bf86d5d` | 0 | 42.61 | 4070481920 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | 300000 local |
| 084 `Wide/InitialCurveBranch.lean` | `45ebd8f90dd47722adb36af792745c3bcdc6d0c1ef718e7fcf4f36dfb515e1a3` | 0 | 43.37 | 4059197440 | 0 | `9416a8c93` + source SHA | 1 reports, P/C/Q only | 300000 local |
| 085 `Wide/InitialCurve.lean` | `dce9f637cd7b50d4962e7e09432dd43ed8966c2b2750b7720a2320e745d4415e` | 0 | 42.15 | 4054753280 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 300000 local, 300000 local |
| 086 `Wide/Initial.lean` | `7e74ef9f528d196f712641c579b530cee93fb8e1a0e7eb96ababd2397c7ea509` | 0 | 42.45 | 4076519424 | 0 | `9416a8c93` + source SHA | 2 reports, P/C/Q only | 300000 local |
| 087 `WideTower.lean` | `f55bd736f0e8bb3fedda8c862bf8311fe3be609b17b72a01f0e476b33c34c538` | 0 | 44.5 | 4054077440 | 0 | `9416a8c93` + source SHA | 5 reports, P/C/Q only | default (200000) |
| 088 `Wide/Instances.lean` | `7a7612bf7f5c5d7e03c3ba20706ce0e7ce8f1b69fa57410385e51b3e2a4cd8ca` | 0 | 41.64 | 4092522496 | 0 | `9416a8c93` + source SHA | 3 reports, P/C/Q only | default (200000) |
| 089 `Wide/Regression.lean` | `5c4b7d447452ba43590d4e6539a473e192214bacc16a26a98bef91b879ec9b27` | 0 | 46.52 | 4072841216 | 0 | `9416a8c93` + source SHA | 4 reports, P/C/Q only | default (200000) |

## Failed attempts and replacements

- Attempt 001, `Wide.InitialEncoder`: The overlap theorem requires Fintype K, omitted in the first extraction. Added the explicit finite-field instance; replaced by attempt 002. No statement threshold or cap changed. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 004, `Wide.GRSConversion`: Two declarations exceeded default elaborator recursion depth after the extraction omitted the original module maxRecDepth 100000; retained that original setting locally on those declarations. Replaced a tower-definitional map-zero step by explicit map_zero for generic K. Replaced by attempt 005; no heartbeat or memory-cap increase. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 005, `Wide.GRSConversion`: The local option was misplaced after a doc comment; deeper elaboration then timed out in projection/completeness unification. Removed the recursion overrides, supplied explicit field/dimension arguments, and used targeted projection simplification instead of broad definitional reduction. Replaced by attempt 006, at default heartbeats and recursion depth. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 006, `Wide.GRSConversion`: Only the final completeness projection still exceeded default recursion depth at change. Replaced change with simp only [exactFinalGRSConversion], keeping the natural-basis polynomial opaque and the explicit n := 256 application. Replaced by attempt 007. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 028, `Wide.HenselWeights`: Nullary counterexample polynomial had no inferable field after generalization; explicit E added to its uses. No premise change. Replacement attempt 034 passes on NUC. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 029, `Wide.HenselWeights`: NUC Lean memory exception during import, before any axiom report; isolated by probes 030–033. Same fixed Lean limit and hard cgroup cap, with reclaimed private-cache pages, passes on attempt 034. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 030, `NucImportProbe`: Import-only HenselRecurrence probe reaches the fixed Lean memory limit; minimal Mathlib probe 031 identifies the cause. Unchanged private segments in a fresh, tighter cgroup cache view resolve it in 033–034. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 031, `NucMathlibProbe`: Minimal import Mathlib exceeds the unchanged Lean -M4500 limit on NUC; isolates failure to import footprint, not Hensel declarations. Module-mode import probe 032 succeeds but cannot import legacy V7 modules; testing unchanged private object segments charged to a tighter cgroup in 033. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 040, `Wide.FixedBranchCurve`: Namespace-prefix substitution incorrectly renamed the unchanged cached Incidence namespace; restored AspisK1.V7ExactCorrelatedAgreementIncidence and made namespace replacement token-bounded, also protecting WeightedPigeonhole. Replaced by attempt 041. Error-generated sorryAx reports are rejected, not proof evidence. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 042, `Wide.ConcreteBranch`: ConcreteBranch formerly received lane-normalization lemmas through ReleasedLift. The generic ReleasedLift deliberately has smaller imports; added an explicit Wide.Agreement import, whose generic lemmas already passed attempt 014. Replaced by attempt 043; no statement change. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 045, `Wide.Terminal`: Stopped after 446.11 seconds of total scope wall time: the 1 GiB soft memory limit throttled a worker with about 820 MiB anonymous RSS while Lake retained about 70 MiB anonymous RSS. Last observed Lean RSS 4,031,276 KiB; timed peak/swaps were not captured on scope termination (MemorySwapMax=0 was enforced). Resolve LEAN_PATH with lake env first, let Lake exit, then run the identical Lean binary/flags; all limits unchanged. Replaced by attempt 046 with command tracing to localize any further stall. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 046, `Wide.Terminal`: Without the Lake parent, tracing located the stall in the final reconstruction declaration (last observed anonymous RSS about 923 MiB, over the 1 GiB scope working limit once other charges are included). Replace broad simp after specialization by the named substituteCandidate_weightedBivariatePolynomial rewrite and exact root. Statement, heartbeats and memory limits unchanged; replaced by attempt 047. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 047, `Wide.Terminal`: The named rewrite alone still left the asynchronous proof worker throttled at the 1 GiB soft limit (observed anonymous RSS about 897 MiB). Stop the Lean process alone to retain timed metrics. Lean source confirms Elab.async defaults to true even with -j1; replace that scheduling mode with -DElab.async=false and remove diagnostic command tracing. No limit or theorem statement is changed; replacement attempt 048. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 048, `Wide.Terminal`: Synchronous elaboration still reached soft-limit throttling. Stopped the process and replaced it with a scratch copy containing flushed per-step diagnostic checkpoints (attempt 049), with the same mathematical statements, cap and scheduling mode. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 049, `NucTerminalProbe`: Scratch checkpoint probe was itself throttled before emitting a checkpoint; no localization or proof claim. The measured live working set exceeded the artificial 1 GiB MemoryHigh throttle. Review keeps -M4500 and MemoryMax=7G unchanged, no swap, and uses MemoryHigh=1280M (still below the original 5G throttle). Validate the import footprint on the previously successful minimal probe, attempt 050, before the changed Terminal proof. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 051, `Wide.Terminal`: At the reviewed soft threshold, the Terminal declaration still grew its working set into throttling (last observed anonymous RSS about 1,143 MiB); hard limits unchanged. Stop for a non-compiling built-in dbg_trace checkpoint probe (052), avoiding the extra IO-tactic compilation of probe 049. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 052, `NucTerminalProbe`: Built-in checkpoint probe also reached sustained throttling before useful output. The partial cache view left public Mathlib pages charged outside the scope while forcing all heap growth into a small reclaimable budget. Replace it with unchanged copies of all Mathlib object segments, and a 3G reclaim threshold (below the original 5G); preserve -M4500, MemoryMax=7G and zero swap. Validate this changed cache layout with minimal import probe 053. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 054, `Wide.Terminal`: The full-cache layout exposed a reclaim loop after the live heap grew to about 2.87 GiB: user CPU time stayed near 12 seconds while kernel time increased. Stop before ten minutes; isolate the generic reconstruction prelude and theorem-type elaboration in scratch probe 055. No limit increase and no proof claim. Prelude/type probe 055 passes; isolate the body with built-in checkpoints under the full-cache layout in 056. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 056, `NucTerminalProbe`: The full-body checkpoint probe still entered reclaim without visible checkpoints. The interpolant index is a huge dependent finite product; next diagnostic lowers maxRecDepth to 2048 and maxHeartbeats to 30000 and line-buffers output to catch unintended unfolding early. Original target limits are not increased; replacement probe 057. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 057, `NucTerminalProbe`: Lower recursion/heartbeat diagnostic ceilings and line buffering did not localize the growth. Stop and use a deliberately failing short prefix through challenge packaging (058), preserving Lake’s compiler environment (binary, sysroot, paths and library paths), with Lake exiting before Lean starts. No cap increase. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 058, `NucTerminalPrefix`: Intentional prefix diagnostic stops at candidate-root entry in 40.31 seconds without pathological growth. Extend the prefix through the candidate-root proof, preserving all resource limits and Lake compiler environment; replacement probe 059. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 059, `NucTerminalPrefix`: Intentional prefix diagnostic checks the full candidate-root proof then stops at outer-count entry in 40.13 seconds. Extend through weighted branch selection; replacement probe 060. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 060, `NucTerminalPrefix`: Intentional prefix diagnostic elaborates through weighted branch selection in 40.48 seconds. These deliberately failing prefixes do not certify kernel checking. Extend through local reconstruction to isolate final packaging; replacement probe 061. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 061, `NucTerminalPrefix`: Intentional prefix diagnostic elaborates through the complete component reconstruction in 40.57 seconds. Replace final broad omega in Terminal with Nat.le_succ and Nat.le_add_left transitivity on selectedLarge, avoiding unrelated finite-index hypotheses; full target replacement attempt 062. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 062, `Wide.Terminal`: Replacing the final arithmetic tactic did not change the full-declaration memory growth; stopped at 82.89 seconds with zero swaps. Prefixes 058–061 elaborate, but do not certify kernel checking. Split the proof into opaque symbolic root, abstract challenge-set reconstruction, and terminal packaging, following the already split V7 initial proof. First compile the new FinalRoot helper (063); hard limits remain unchanged. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 066, `Wide.FinalCurveBranch`: The split localizes growth to FinalCurveBranch, whose added step rewrites Fintype.card (Fin 262144). Stop at 97.79 seconds, zero swaps. Replace concrete cardinality rewriting with card_fin_lt_of_budget, proved first for symbolic domainSize, curveDegree, budget and count in Wide.Cardinality; use its opaque application in both final and initial packaging. Compile this smallest helper before the dependent bridge. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 068, `Wide.FinalCurveBranch`: The opaque cardinality application exposes maximum recursion depth at FinalCurveBranch line 92, without memory-pressure termination. Reject the failed sorryAx report. Isolate just the concrete cardinality application in a tiny scratch file, with explicit Nat arguments and reducible transparency, before changing the bridge; diagnostic 069. Diagnostic 070 compiles the concrete application in 1.08 seconds. Apply its explicit arguments and with_reducible transparency to the bridge in 071, avoiding eager normalization while solving implicit Nat arguments. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 069, `NucCardinalityApply`: Scratch diagnostic had a layout error: arguments after with_reducible exact were indented before the nested exact command column. Correct indentation and rerun the changed diagnostic; no proof or resource-limit change. Replacement 070. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 071, `Wide.FinalCurveBranch`: Explicit Nat arguments and reducible elaboration still leave full FinalCurveBranch proof checking in memory reclamation; stopped at 93.44 seconds, zero swaps. Isolate the concrete cardinality theorem under the complete FinalSelection import environment (072), to distinguish imported instance paths from the surrounding branch proof. No cap increase. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 072, `NucCardinalityApply`: The same tiny concrete application stalls only after importing FinalSelection, isolating the discrepancy to the import environment rather than branch reconstruction. Stop before ten minutes, zero swap enforced. Recompile the symbolic Cardinality lemma with import Mathlib, matching the Nat instance environment used by agreement statements (073); its statement and proof remain unchanged. Then recheck the concrete application before the bridge. (Failed elaboration axiom reports are not proof evidence.)
- Attempt 074, `NucCardinalityApply`: Matching the full Mathlib import for the helper is insufficient: the isolated full-import application still grows. Stop the diagnostic; inspect fully explicit elaborated types and instance paths without completing the concrete proof (075). The prior inference about matching Nat instance imports is not yet established as the cause. Inspection 075 identifies the exact mismatch: the concrete Fin 262144 uses SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat, while the generic helper uses Fin.fintype. Replacement 076 quantifies over the Fintype instance and relates it to Fin.fintype via Fintype.card_congr (Equiv.refl _), avoiding enumeration. No mathematical premise is restricted. (Failed elaboration axiom reports are not proof evidence.)

## Endpoint axiom audits

Every successful final-source row records the number of `#print axioms` reports and their P/C/Q-only result. The corresponding commands remain in each Lean source; complete raw outputs are retained in the external evidence directory. The endpoint outputs are reproduced here.

- Attempt 010: `AspisWide.EncoderRegression.initialEncoder_eq_v7` — propext, Classical.choice, Quot.sound; `AspisWide.EncoderRegression.finalEncoder_eq_v7` — propext, Classical.choice, Quot.sound.
- Attempt 080: `AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable` — propext, Classical.choice, Quot.sound; `AspisWide.Terminal.exactV7FinalPublishedOneFoldCurveDecodability` — propext, Classical.choice, Quot.sound.
- Attempt 086: `AspisWide.Terminal.exactV7InitialWidth29CurveDecodable` — propext, Classical.choice, Quot.sound; `AspisWide.Terminal.exactV7InitialPublishedWidth29CurveDecodability` — propext, Classical.choice, Quot.sound.
- Attempt 087: `AspisWideTower.qm31_wideU_not_isSquare` — propext, Classical.choice, Quot.sound; `AspisWideTower.wideExact_card` — propext, Classical.choice, Quot.sound; `AspisWideTower.wideExact_natCast_ne_zero_of_pos_of_lt_characteristic` — propext, Classical.choice, Quot.sound; `AspisWideTower.wideExact_two_ne_zero` — propext, Classical.choice, Quot.sound; `AspisWideTower.qm31_to_wide_injective` — propext, Classical.choice, Quot.sound.
- Attempt 088: `AspisWide.Instances.wideInitialWidth29CurveDecodable` — propext, Classical.choice, Quot.sound; `AspisWide.Instances.wideFinalDegreeThreeCurveDecodable` — propext, Classical.choice, Quot.sound; `AspisWide.Instances.unchangedChallengeCaps` — none.
- Attempt 089: `AspisWide.Regression.qm31InitialWidth29CurveDecodable` — propext, Classical.choice, Quot.sound; `AspisWide.Regression.qm31FinalDegreeThreeCurveDecodable` — propext, Classical.choice, Quot.sound; `AspisWide.Regression.initialResult_eq_v7` — propext, Classical.choice, Quot.sound; `AspisWide.Regression.finalResult_eq_v7` — propext, Classical.choice, Quot.sound.

## Replay 2026-10-06

Replay source revision: `1aa58a9e9dac2c9c9cc6b6b09998e4a38d25a2c4`.
Worktree: `/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922`.
Separate build-host workspace: `/home/dombarker/project-offloads/aspis-wide-replay-20261006`.
The author's workspace is read-only evidence. Its Wide objects are used only
for import-footprint measurement, never as fallback during source compilation.
All 48 source files were extracted from the commit and checked byte-for-byte
against the worktree; the replay object directory started empty.

Import-only probes ran sequentially with `-j1 -DElab.async=false`, GNU
`/usr/bin/time -v`, a 600-second timeout and one systemd scope per target.
Measurement used no Lean `-M` option; memory was bounded by the scope:
`MemoryHigh=6500M`, `MemoryMax=7G`, `MemorySwapMax=0`.

| Import-only target | Exit | Wall seconds | Peak RSS KiB | Swaps | Cgroup swap peak |
|---|---:|---:|---:|---:|---:|
| `import Wide.Terminal` | 0 | 2.73 | 6711216 | 0 | 0 |
| `import Wide.Instances` + `import Wide.Regression` | 0 | 2.76 | 6868880 | 0 | 0 |

After these measurements, the source-replay setting is fixed at **`-M7000`**,
about 292 MiB above the larger measured import RSS (6707.89 MiB). The scope
limits remain unchanged. This is an import-based setting, not a retry after
a failing proof. The full source replay below subsequently passed at this setting.

### Environment and exact source command

Lean binary: `/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`.
Version: `Lean (version 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)`.
Binary SHA-256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.

Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`.
The 267 copied V7 `.olean` files match every hash in the author’s
`evidence/pinned-object-hashes.json`. The older NUC project-object root is
excluded from this replay. No dependency build or `lake build` was run.

The complete ordered `LEAN_PATH` for source compilation is:

```text
/home/dombarker/project-offloads/aspis-wide-replay-20261006/objects
/home/dombarker/project-offloads/aspis-wide-replay-20261006/pinned-v7
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/Cli/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/batteries/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/Qq/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/aesop/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/proofwidgets/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/importGraph/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/plausible/.lake/build/lib/lean
/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib/.lake/build/lib/lean
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean
```

Import probes append `/home/dombarker/project-offloads/aspis-wide-port-20261005/objects`
as entry 13; that entry is absent from all source-replay commands.

Object-set listings are sorted UTF-8 lines `SHA256  size_bytes  relative_path`,
including `.olean`, `.olean.private`, `.olean.server` and `.ir` files.
Below, entry numbers refer to the ordered search path above. Listings and raw
compiler evidence remain in the replay workspace’s `evidence/` directory.

| Search-path entry | Artifact count before replay | Listing SHA-256 |
|---:|---:|---|
| 1 | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| 2 | 267 | `172f987aaec752424794eaa056f9d363e71ef7ba3ef1de67a24367f3a94439b0` |
| 3 | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| 4 | 753 | `dcf5877b3555302d05232f35a344b091b9eb82c11990bd68b97ddef87a01a716` |
| 5 | 56 | `40e3dbf935ce2159a6457a1a75c30a2c890066a98ebfd97b3ec77c510b21714d` |
| 6 | 528 | `d8fe51972479b58153267b704bdfe919b14b451be6462b3dc7148b9b6bfc6b4b` |
| 7 | 92 | `d6ecba0cc4c2ee3eb0d4a64eb00e52e97d14c23e9afbec603a72108679f97745` |
| 8 | 84 | `11ea7e2e4effd0eba1167c5c4ceb3be0c580ee230116ff3ad9fb3962e0221f83` |
| 9 | 16 | `bf7c59f945fe4918f90d1568d489c545e83f81560fd60f432a04208d8979acff` |
| 10 | 52 | `58fedb95c7a159012d47156551273318cf6ec9d0198a09a4c9de50c4cb587ef6` |
| 11 | 33070 | `ed83c0c1d17caac84c70031f5bfc5fdf04845acfcf647524071211d5527f3ce4` |
| 12 | 9726 | `d813aff42029d95af7f8b81d8c373ed1c9f864a5af8abdf103d31349ccdb4d86` |

Entry 1 was empty; entry 2 is the copied V7 set; entry 11 is Mathlib.
Entries 3–10 are the exact cached Mathlib dependencies; entry 12 is the
toolchain library. Listing files are named `object-set-00.txt` through
`object-set-11.txt` (zero-based).

Before every job, a cgroup inventory checked populated finite caps, avoided
double-counting capped descendants, and checked that no other Lean process
was running. At the import probes, existing caps totaled 44.375 GiB; with
the new 7 GiB scope this was 51.375 GiB, below the 55 GiB host limit.

Exact command template (with the captured compiler environment restored and
the ordered `LEAN_PATH` above):

```sh
systemd-run --user --scope --quiet --unit="aspis-wide-replay-$tag" \
  -p MemoryHigh=6500M -p MemoryMax=7G -p MemorySwapMax=0 \
  python3 /home/dombarker/project-offloads/aspis-wide-replay-20261006/replay.py \
  inside "$tag" "$source" "$output" 0
```

The scope wrapper executes, in the replay workspace:

```sh
/usr/bin/time -v -o "evidence/$tag.time" \
  timeout --signal=TERM --kill-after=10 600 \
  /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -j1 -M7000 -DElab.async=false \
  -R /home/dombarker/project-offloads/aspis-wide-replay-20261006/sources \
  -o "$output" "$source"
```

For each job, `evidence/$tag.json` records the full expanded command, exact
source SHA-256, all search-path entries, exit status, GNU time metrics,
effective cgroup limits, cgroup memory/swap peaks and OOM counters, and the
literal axiom output. `$tag.stdout` and `$tag.time` retain raw output.

### Footprint discrepancy

The discrepancy remains **unexplained**. The pinned V7 hashes and Lean/Mathlib
revisions match the author’s records; no current Mathlib object has an mtime
later than 2026-10-05 23:40 UTC. The author’s logged final commands and this
replay both disable asynchronous elaboration. Historical full Mathlib object
hashes and the successful per-job copied cache views are unavailable, so
mtime and revision agreement do not establish byte-for-byte historical
Mathlib equivalence.

The author used fresh copied Mathlib views with `MemoryHigh=3G`; this replay
reads the pinned Mathlib path directly and uses `MemoryHigh=6500M`.
A live `Wide.RegularRing` sample had RSS 6,705,352 KiB, file PSS 6,255,352 KiB,
anonymous PSS 447,840 KiB and swap 0. Its mappings contained 31,256 `.olean`
segments, including 12 newly compiled Wide objects and 29 pinned V7 objects,
with no mappings from the author’s Wide object directory. This demonstrates
that mapped file pages dominate the measured footprint; it does **not**
establish why the historical `-M4500` run succeeded at about 4.0 GB.

### Part A: complete source replay

**PASS: 48/48 source files**, in the dependency order below, with 303 clean
`#print axioms` reports. No proof source was changed. Every row uses source
revision `1aa58a9e9dac2c9c9cc6b6b09998e4a38d25a2c4`, `-M7000` and the scope
limits above. GNU time reports peak RSS in KiB (multiply by 1024 for bytes).
All cgroup swap peaks and OOM-kill counts were zero. The maximum measured RSS
was 7,003,368 KiB (6.679 GiB), in `Wide.Interpolation`.

The audit column gives the number of literal reports reproduced below;
`PCQ` means exactly `[propext, Classical.choice, Quot.sound]`, with a subset
where the output says otherwise. Raw files use the numbered target tag,
for example `01-Wide-InitialEncoder.stdout` and `.time`.

| Order / target | Source SHA-256 | Exit | Wall | Peak RSS KiB | Swaps | Audit |
|---|---|---:|---|---:|---:|---|
| 01 `Wide/InitialEncoder.lean` | `518bf5e70161f11981f3c0b97f95f88efe08e0d3065d54848079e507138552b2` | 0 | 0:03.08 | 6728984 | 0 | 4, PCQ/subset |
| 02 `Wide/FinalEncoder.lean` | `6ae59a2d5f9d2d5d56b70ac6c67121d3bcb26f42470bafb3e2d798429590488f` | 0 | 0:04.35 | 6755612 | 0 | 4, PCQ/subset |
| 03 `Wide/EncoderLinearity.lean` | `14fab916cb20666ee40cf6e62281c4282cfd36c23af38fca4042dce249c8ee5f` | 0 | 0:03.72 | 6747336 | 0 | 4, PCQ/subset |
| 04 `Wide/GRSConversion.lean` | `df621ca75572edf4e5291d1c64b802a158303e404a5b7f0ec3e63630acd39255` | 0 | 0:03.87 | 6746236 | 0 | 16, PCQ/subset |
| 05 `Wide/MultiplicityThreeGS.lean` | `73252b85be6db2b7a0180d9f942e1872a75a57e6257dfb36124139bb27f277b5` | 0 | 0:08.77 | 6989380 | 0 | 19, PCQ/subset |
| 06 `Wide/Interpolation.lean` | `834bdc8c5b3d16c42d25e55d9be9895e2d6ed2a035c949487369667bbe3dec4a` | 0 | 0:07.98 | 7003368 | 0 | 8, PCQ/subset |
| 07 `Wide/Agreement.lean` | `783b14e3f958071f52a7dafe8d4bb76a4360e7a49e4de3a22f87eda2023b0338` | 0 | 0:03.34 | 6751896 | 0 | 8, PCQ/subset |
| 08 `Wide/Factors.lean` | `44cbdc81be8d8aa519c170fbd511dc4cd70885bfe0a1762f7e3de97d82e647f7` | 0 | 0:05.73 | 6758064 | 0 | 10, PCQ/subset |
| 09 `Wide/Smooth.lean` | `236ddbdc270bc67d62b1deea5d5a1ce01cdd8884584fc54c9a002c783735dc7e` | 0 | 0:06.77 | 6771324 | 0 | 10, PCQ/subset |
| 10 `Wide/Hensel.lean` | `92342560420c536f7b622c2c0031d4a233c545af82e1392409446bf7ed8ff890` | 0 | 0:04.42 | 6755888 | 0 | 5, PCQ/subset |
| 11 `Wide/LocalFactors.lean` | `d6225243413d8ac80843063d3f1d99468f6a51a852083ce8a980de1a3252fdb7` | 0 | 0:03.85 | 6747864 | 0 | 7, PCQ/subset |
| 12 `Wide/FunctionField.lean` | `c4bfa3d14cbf56ca5686be890a375746e6711d57b029514cff81a1b5ab56a41c` | 0 | 0:05.33 | 6754064 | 0 | 4, PCQ/subset |
| 13 `Wide/PowerSeriesLift.lean` | `2932fdc22cdf579950bb29e8c822e0c1e23f56bcb1c0e99b336928874e874c93` | 0 | 0:07.45 | 6746836 | 0 | 3, PCQ/subset |
| 14 `Wide/RegularWeights.lean` | `7b583549cc3d32cb23c569ab4643243449e0fd0567694284452944e4c2660b6e` | 0 | 0:05.14 | 6770576 | 0 | 15, PCQ/subset |
| 15 `Wide/RegularRing.lean` | `51023907cbdb8889f21187fc6cbf0bede997bc01eb9ac65f4f1c637a91cb9310` | 0 | 0:06.14 | 6767368 | 0 | 18, PCQ/subset |
| 16 `Wide/RegularZeroCount.lean` | `32ea002db6bebd19d3628efd91f974bf8a95bcdff2bd91637ac1341472478912` | 0 | 0:05.95 | 6756508 | 0 | 8, PCQ/subset |
| 17 `Wide/HenselCombinatorics.lean` | `b0171895d4a4a6acaaf06e92d5360457e4ac55e905616eb55482750b04c3f001` | 0 | 0:05.09 | 6764552 | 0 | 16, PCQ/subset |
| 18 `Wide/HenselRecurrence.lean` | `46658b8d22df6786e1442da16470ddf8e49bb6d2fef4c6d9ae4396f4095fb148` | 0 | 0:03.54 | 6739252 | 0 | 1, PCQ/subset |
| 19 `Wide/RegularEvaluation.lean` | `a116ef5450c482aa291df40e008840305ffde91d856b3b8bce3d34aef8ee874d` | 0 | 0:05.21 | 6754436 | 0 | 5, PCQ/subset |
| 20 `Wide/RegularHensel.lean` | `e2c4af177e5e802d43c4d81db90b182002bfcd6850ae344314382202dc0f661d` | 0 | 0:05.21 | 6749416 | 0 | 5, PCQ/subset |
| 21 `Wide/FactorBudgets.lean` | `9703a2245522f18e90b29b84ab353c92630daa56487381db92f2d4fedb07d196` | 0 | 0:06.02 | 6777144 | 0 | 16, PCQ/subset |
| 22 `Wide/HenselWeights.lean` | `7f95af03f66b47170eb3efa75bcc17e5a15b59977ee9b4b661c031466109ced8` | 0 | 0:08.34 | 6777428 | 0 | 21, PCQ/subset |
| 23 `Wide/HenselIntegralLift.lean` | `ecd52be61f8c171a699e4ef69963aeb6a7a90b72416a8bf7b41f347780018a80` | 0 | 0:15.96 | 6812336 | 0 | 15, PCQ/subset |
| 24 `Wide/HenselSpecialization.lean` | `d7e48ffa237f8f31a0362986fb3b8b87afedbb49c33aa0460e12e700991a3b2f` | 0 | 0:06.42 | 6768228 | 0 | 13, PCQ/subset |
| 25 `Wide/FiniteBranch.lean` | `cf72efcdc93a02a613250adde3c5ae29981005cd061aee801b5e1c19f6af28f0` | 0 | 0:08.67 | 6765520 | 0 | 8, PCQ/subset |
| 26 `Wide/BranchEvaluation.lean` | `d23b7e1579f449a5f2f538467f5ed06f443b65a2877152e6226f5b0e672f5f41` | 0 | 0:08.31 | 6777632 | 0 | 11, PCQ/subset |
| 27 `Wide/AmbientCurve.lean` | `23d46d5d838ec039207e0da64fbf75f467e3d130ef387770df950a54826a17bc` | 0 | 0:02.92 | 6751584 | 0 | 3, PCQ/subset |
| 28 `Wide/Cardinality.lean` | `373ba7d10692b6ddad737919145cc3b1c2672ff22716ae7ff664939740b82fb9` | 0 | 0:00.64 | 1545812 | 0 | 2, PCQ/subset |
| 29 `Wide/FixedBranchCurve.lean` | `dfd6574eaa4a7777253b2ca7061d1661176d27998669c29365aea434f716ae53` | 0 | 0:02.94 | 6749612 | 0 | 1, PCQ/subset |
| 30 `Wide/ReleasedLift.lean` | `fd04f0b241ee320b200be7340f97017982adba2fa1bb59131b621adc704d555d` | 0 | 0:03.28 | 6743696 | 0 | 4, PCQ/subset |
| 31 `Wide/ConcreteBranch.lean` | `2af45f9a045e4d91a196d59957fb5728defe555469e2ec0ae6284b586204d1a9` | 0 | 0:03.58 | 6768528 | 0 | 2, PCQ/subset |
| 32 `Wide/EncoderRegression.lean` | `4535cbb3a56a47bbec7f95175fa30c4ccf69e5788018bc5b505119283e832d48` | 0 | 0:02.90 | 6864960 | 0 | 2, PCQ/subset |
| 33 `Wide/OuterSelection.lean` | `ae6bd2a461611ab79ecc0c67bae571887cbef031505629e90bb4004e4ebc45b7` | 0 | 0:05.04 | 6782304 | 0 | 5, PCQ/subset |
| 34 `Wide/FinalRoot.lean` | `aa8ad2e10b8c455cdbf9a08c11f0650aacf849fe66750bc7118f870fed988ad3` | 0 | 0:03.13 | 6751848 | 0 | 2, PCQ/subset |
| 35 `Wide/FinalBranch.lean` | `38bfe106ddfc3c9fff5893d48aa31236022bbdfe0e80951a4880a8e9b16e86e5` | 0 | 0:02.98 | 6748372 | 0 | 1, PCQ/subset |
| 36 `Wide/FinalSelection.lean` | `f54b193d353e0f706a98d88fbcb3b059cb9713bc40ac54df8111117988ba8ec9` | 0 | 0:03.00 | 6752804 | 0 | 1, PCQ/subset |
| 37 `Wide/FinalCurveBranch.lean` | `27fc6fc66a96534662506fc17171936cada63ab2c0dc4e1f031a6e4e966733fa` | 0 | 0:02.95 | 6747936 | 0 | 1, PCQ/subset |
| 38 `Wide/FinalCurve.lean` | `a65691e03f23e30147f549c86f954c8046192f182b27d1acd1b4aa2c181ef416` | 0 | 0:03.07 | 6748528 | 0 | 2, PCQ/subset |
| 39 `Wide/Terminal.lean` | `943d9b78b162fe3f60709309db5bd28ec9acd99088f90eb6203ea49bb26b0daf` | 0 | 0:03.13 | 6760572 | 0 | 2, PCQ/subset |
| 40 `Wide/InitialRoot.lean` | `2c0c645d5892f2d34f4162ff8b97caa6da39956e7d68cc09e5244eb3bbe06adf` | 0 | 0:03.10 | 6759972 | 0 | 2, PCQ/subset |
| 41 `Wide/InitialBranch.lean` | `c01ee2940d3149a9c7353625e23e2dd9039957360c809b1e7f5434c5aa09f81e` | 0 | 0:03.19 | 6748784 | 0 | 1, PCQ/subset |
| 42 `Wide/InitialSelection.lean` | `1c1cadb34447617d5927c4146c8368d924741c63b1544abdb88f82398bf86d5d` | 0 | 0:03.25 | 6752008 | 0 | 1, PCQ/subset |
| 43 `Wide/InitialCurveBranch.lean` | `45ebd8f90dd47722adb36af792745c3bcdc6d0c1ef718e7fcf4f36dfb515e1a3` | 0 | 0:03.19 | 6748584 | 0 | 1, PCQ/subset |
| 44 `Wide/InitialCurve.lean` | `dce9f637cd7b50d4962e7e09432dd43ed8966c2b2750b7720a2320e745d4415e` | 0 | 0:03.28 | 6749588 | 0 | 2, PCQ/subset |
| 45 `Wide/Initial.lean` | `7e74ef9f528d196f712641c579b530cee93fb8e1a0e7eb96ababd2397c7ea509` | 0 | 0:03.24 | 6753096 | 0 | 2, PCQ/subset |
| 46 `WideTower.lean` | `f55bd736f0e8bb3fedda8c862bf8311fe3be609b17b72a01f0e476b33c34c538` | 0 | 0:05.58 | 6746804 | 0 | 5, PCQ/subset |
| 47 `Wide/Instances.lean` | `7a7612bf7f5c5d7e03c3ba20706ce0e7ce8f1b69fa57410385e51b3e2a4cd8ca` | 0 | 0:03.34 | 6759848 | 0 | 3, PCQ/subset |
| 48 `Wide/Regression.lean` | `5c4b7d447452ba43590d4e6539a473e192214bacc16a26a98bef91b879ec9b27` | 0 | 0:03.16 | 6899236 | 0 | 4, PCQ/subset |

<details>
<summary>Complete per-file axiom output from this source replay</summary>

`Wide/InitialEncoder.lean`:

```text
'AspisWide.InitialEncoder.two_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.InitialEncoder.exactInitialPolynomialPair_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.InitialEncoder.exactInitialEncoderCircleRealization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.InitialEncoder.exactInitialEncoder_overlap_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/FinalEncoder.lean`:

```text
'AspisWide.FinalEncoder.exactFinalLinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FinalEncoder.exactFinalEncoder_overlap_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FinalEncoder.exactFinalEncoder_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FinalEncoder.exactInitialEncoder_eq_circleLift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/EncoderLinearity.lean`:

```text
'AspisWide.Agreement.exactInitialEncoder_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactInitialLinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactInitialEncoder_messageCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactFinalEncoder_messageCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/GRSConversion.lean`:

```text
'AspisWide.GRSConversion.exactFinalGRSConversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactFinalEncoder_eq_grs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactFinalAgreementCount_eq_grs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactFinalThreshold_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactFinalMessagePolynomial_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.GRSConversion.exactFinal9558_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactCircleGRSPoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactCircleGRSMultiplier_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactCircleGRSPolynomial_degree_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactCircleGRSPolynomial_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactInitialEncoder_coordinate_grs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactInitialGRSConversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactInitialEncoder_eq_grs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactInitialAgreementCount_eq_grs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactInitialThreshold_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.GRSConversion.exactInitial38230_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/MultiplicityThreeGS.lean`:

```text
'AspisWide.MultiplicityThreeGS.exactInitialAmbientDegreeConvention' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalAmbientDegreeConvention' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalInterpolationBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.MultiplicityThreeGS.exactInitialInterpolationBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exists_nonzero_interpolationKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exists_exactFinalInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exists_exactInitialInterpolation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.interpolationMultiplicityThree_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.interpolationSubstitute_eq_zero_of_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalPolynomialAgreement_card_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalRootCandidates_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalGSDecode_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalGSDecode_length_le_99' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactFinalMultiplicityThreeGS' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.MultiplicityThreeGS.exactInitialPolynomialAgreement_card_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactInitialRootCandidates_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactInitialGSDecode_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.MultiplicityThreeGS.exactInitialGSDecode_length_le_100' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MultiplicityThreeGS.exactInitialMultiplicityThreeGS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Interpolation.lean`:

```text
'AspisWide.Interpolation.curveConstraintPolynomial_eq_zero_of_mem_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Interpolation.interpolationConstraint_specializeCurveCoefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Interpolation.exists_curveCoefficientPolynomial_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Interpolation.zeroCurveSpecializations_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Interpolation.specializeCurveCoefficients_mem_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Interpolation.exists_nonzero_curveInterpolationKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Interpolation.exactInitialCurveInterpolationBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Interpolation.exactFinalCurveInterpolationBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/Agreement.lean`:

```text
'AspisWide.Agreement.exactInitialEncoder_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactInitialEncoder_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactFinalEncoder_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactFinalEncoder_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exists_exactInitialCurveInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exists_exactFinalCurveInterpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Agreement.exactFinalValidCandidate_substitute_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Agreement.exactInitialValidCandidate_substitute_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Factors.lean`:

```text
'AspisWide.Factors.specializeChallenge_curveTrivariatePolynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Factors.candidate_linearFactor_dvd_of_substitute_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Factors.curveTrivariatePolynomial_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.weightedBivariatePolynomial_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.curveTrivariatePolynomial_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.curvePrimeFactors_product_associated' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.positiveYPrimeFactors_card_le_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.sum_positiveYPrimeFactors_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.exists_positiveDegree_primeFactor_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Factors.exists_frequent_positiveDegree_primeFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Smooth.lean`:

```text
'AspisWide.Smooth.curvePrimeFactor_resultant_derivative_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Smooth.separabilityCertificate_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Smooth.separabilityCertificate_xNatDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Smooth.exists_exactV7_uniformSmoothEvaluationPoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Smooth.resultant_eq_zero_of_common_root_of_natDegree_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Smooth.simpleSpecializedRoot_of_certificate_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Smooth.nonsimpleChallengeSet_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Smooth.exactV7Initial_nonsimpleChallengeSet_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Smooth.exactV7Final_nonsimpleChallengeSet_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Smooth.simpleSpecializedRoot_of_not_mem_nonsimpleChallengeSet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Hensel.lean`:

```text
'AspisWide.Hensel.exists_powerSeries_root_of_monic_simple_constant_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Hensel.exists_powerSeries_root_of_unitLeading_simple_constant_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Hensel.exists_adic_root_of_simple_approximation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Hensel.exists_powerSeries_root_of_simple_constant_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Hensel.powerSeries_root_unique_of_simple_constant_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/LocalFactors.lean`:

```text
'AspisWide.LocalFactors.bivariatePrimeFactors_product_associated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.LocalFactors.exists_leadingCoeff_quotient_of_bivariatePrimeFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.LocalFactors.leadingCoeff_quotient_natDegree_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.LocalFactors.positiveYBivariatePrimeFactors_card_le_natDegree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.LocalFactors.sum_positiveYBivariatePrimeFactors_natDegree_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.LocalFactors.exists_localPrimeFactor_for_simpleSpecializedRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.LocalFactors.exists_frequent_localPrimeFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/FunctionField.lean`:

```text
'AspisWide.FunctionField.localFactorOverRational_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FunctionField.exactV7_localPrimeFactor_derivative_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FunctionField.localBranchRoot_isRoot_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FunctionField.localBranchRoot_not_isRoot_parentDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/PowerSeriesLift.lean`:

```text
'AspisWide.PowerSeriesLift.constantCoeff_comp_localCoefficientPowerSeriesHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.PowerSeriesLift.constantCoeff_liftedGlobalFactor_eval_C' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.PowerSeriesLift.exists_exactV7_fixedBranch_powerSeriesRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/RegularWeights.lean`:

```text
'AspisWide.RegularWeights.localBivariateWeight_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.weightedHomogeneousComponent_top_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularWeights.weightedHomogeneousComponent_mul_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularWeights.weightedTotalDegree_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_multiset_prod_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_C_le_natDegree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_monomial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.localBivariateWeight_le_of_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.iteratedBivariateWeight_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.iteratedBivariateWeight_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularWeights.iteratedBivariateWeight_le_of_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularWeights.iteratedBivariateWeight_modByMonic_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/RegularRing.lean`:

```text
'AspisWide.RegularRing.integralLocalFactor_monic' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralBranchGenerator_isRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralLocalFactor_root_of_localFactor_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralBranchToFunctionField_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.canonicalRegularRepresentative_natDegree_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralBranchSpecialization_eq_eval_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralLocalFactor_coefficientWeight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralLocalFactor_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralLocalFactor_iteratedWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.canonicalRegularRepresentative_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_finset_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_finset_prod_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_mk_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_of_le_natDegree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularRing.integralBranchIteratedWeight_root_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/RegularZeroCount.lean`:

```text
'AspisWide.RegularZeroCount.matrix_det_natDegree_le_of_potentials' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularZeroCount.resultant_natDegree_le_mul_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularZeroCount.canonicalRegularRepresentative_resultant_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularZeroCount.eval_canonicalRegularRepresentative_resultant_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularZeroCount.canonicalRegularRepresentative_resultant_natDegree_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularZeroCount.card_rootPair_specializations_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularZeroCount.integralBranch_eq_zero_of_mul_weight_lt_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularZeroCount.integralBranchToFunctionField_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/HenselCombinatorics.lean`:

```text
'AspisWide.HenselCombinatorics.sum_henselDenominatorExponent_add_positivePartCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.sum_henselDenominatorExponent_le_two_mul_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.sum_henselDenominatorExponent_le_two_mul_sub_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.sum_henselDenominatorExponent_le_two_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.sum_henselDenominatorExponent_le_target_sub_one_of_total_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.clear_hensel_product_denominators' depends on axioms: [propext, Quot.sound]
'AspisWide.HenselCombinatorics.exists_unique_full_part_of_positivePartCount_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.positivePartCount_range_eq_of_coeffProduct_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.convolution_henselExponent_le_two_mul_sub_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.coeff_pow_eq_linear_add_nonlinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.coeff_pow_eq_linear_add_nonlinear_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.coeff_mul_eq_constant_add_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.coeff_eval_eq_derivative_mul_add_nonlinear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.derivative_mul_coeff_eq_neg_nonlinear_of_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.nonlinearEvaluationCoefficientOn_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselCombinatorics.derivative_mul_coeff_eq_neg_nonlinearOn_of_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/HenselRecurrence.lean`:

```text
'AspisWide.HenselRecurrence.exactV7_fixedBranch_coefficient_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/RegularEvaluation.lean`:

```text
'AspisWide.RegularEvaluation.integralBranchToFunctionField_regularizedBranchEvaluation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularEvaluation.integralBranchSpecialization_regularizedBranchEvaluation_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularEvaluation.integralBranchSpecialization_regularizedBranchEvaluation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularEvaluation.regularizedPolynomial_iteratedWeight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularEvaluation.integralBranchIteratedWeight_regularizedBranchEvaluation_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/RegularHensel.lean`:

```text
'AspisWide.RegularHensel.integralBranchToFunctionField_regularizedHenselDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularHensel.exactV7_regularizedHenselDerivative_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.RegularHensel.mem_localPoleChallengeSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularHensel.localPoleChallengeSet_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.RegularHensel.specialization_regularizedHenselDerivative_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/FactorBudgets.lean`:

```text
'AspisWide.FactorBudgets.coeff_equivMvPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FactorBudgets.fixedBranchEvaluationBudget_le' depends on axioms: [propext, Quot.sound]
'AspisWide.FactorBudgets.coeff_weight_le_localBivariateWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.localBivariateWeight_eq_iteratedBivariateWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.localBivariateWeight_specializeEvaluationPoint_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.trivariateXYWeight_curveTrivariatePolynomial_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.trivariateYZWeight_curveTrivariatePolynomial_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.sum_positiveGlobalFactorWeights_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FactorBudgets.sum_positiveGlobalFactorYZWeights_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.sum_positiveLocalFactorWeights_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FactorBudgets.exactInitial_improvedBranchBudget_lt_releaseCap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.exactFinal_improvedBranchBudget_lt_releaseCap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FactorBudgets.exactInitial_incidence_of_branchSelection' depends on axioms: [propext, Quot.sound]
'AspisWide.FactorBudgets.exactFinal_incidence_of_branchSelection' depends on axioms: [propext, Quot.sound]
'AspisWide.FactorBudgets.exactInitial_concurrency_of_branchSelection' depends on axioms: [propext, Quot.sound]
'AspisWide.FactorBudgets.exactFinal_concurrency_of_branchSelection' depends on axioms: [propext, Quot.sound]
```

`Wide/HenselWeights.lean`:

```text
'AspisWide.HenselWeights.derivative_coefficientWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.HenselWeights.integralBranchIteratedWeight_regularizedHenselDerivative_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.leading_mul_constantBranchRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.HenselWeights.shiftedXCoefficientHom_eq_coe_taylor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.coeff_shiftedXCoefficientHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.HenselWeights.coeff_shiftedChallengeCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.HenselWeights.shiftedChallengeCoefficient_natDegree_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.shiftedChallengeCoefficient_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.integralBranchIteratedWeight_shiftedCoefficient_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.coeff_localCoefficientPowerSeriesHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.coeff_liftedGlobalFactor_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.map_regularClearedPowerCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.HenselWeights.map_regularClearedSupportedPowerCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.map_regularClearedSupportedPowerCoefficient_of_specialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.integralBranchToFunctionField_regularClearedHenselCoefficientZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.regularClearedHenselCoefficientZero_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.regularClearedCoefficientProduct_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.regularClearedPowerCoefficient_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.regularClearedSupportedPowerCoefficient_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.nonsaturatedLinearBranch_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselWeights.nonsaturatedLinearBranch_generator_ceiling_ne_leading_add_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/HenselIntegralLift.lean`:

```text
'AspisWide.HenselIntegralLift.map_clearedTail' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.Wide.HenselIntegralLift.0.AspisWide.HenselIntegralLift.nonlinear_supported_exponentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Wide.HenselIntegralLift.0.AspisWide.HenselIntegralLift.positive_shift_exponentBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.map_regularClearedNonlinearEvaluationCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.map_regularClearedNonlinearEvaluationCoefficientOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.map_neg_regularClearedNonlinearEvaluationCoefficientOn_of_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.map_neg_regularClearedNonlinearEvaluationCoefficient_of_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.regularClearedNonlinearEvaluationCoefficient_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.integralBranchToFunctionField_regularLiftedGlobalCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.integralBranchIteratedWeight_localLeading_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.regularLiftedGlobalCoefficient_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.exact_regularizedHensel_structuralBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.regularClearedHenselNext_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.HenselIntegralLift.exists_regularClearedHenselCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselIntegralLift.exists_regularClearedHenselCoefficient_with_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/HenselSpecialization.lean`:

```text
'AspisWide.HenselSpecialization.chosenRegularClearedHenselCoefficient_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.chosenRegularClearedHenselCoefficient_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.specialization_regularizedHenselDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.specialization_chosenRegularClearedHenselCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.chosenRegularClearedHenselCoefficient_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.chosenRegularClearedHenselCoefficient_eq_zero_of_many_specializations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.coeff_fixedBranchRoot_eq_zero_of_chosenRegularCleared_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.coeff_fixedBranchRoot_eq_zero_of_many_specializations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.specializedShiftedCoefficientHom_eq_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.coeff_specializedShiftedCoefficientHom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.integralBranchSpecialization_regularLiftedGlobalCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.shiftedCandidateSeries_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.HenselSpecialization.constantCoeff_specializedLiftedGlobalFactor_derivative_eval_C' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/FiniteBranch.lean`:

```text
'AspisWide.FiniteBranch.trunc_eval_coe_trunc' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FiniteBranch.trunc_eval_coe_trunc_eq_zero_of_isRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FiniteBranch.map_coe_polynomialLiftedGlobalFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FiniteBranch.natDegree_eval_le_localBivariateWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FiniteBranch.polynomialTruncation_isRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.FiniteBranch.polynomialTruncation_isRoot_of_gap_coefficients_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FiniteBranch.fixedBranchRoot_eq_coe_truncation_of_gap_coefficients_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.FiniteBranch.fixedBranchRoot_eq_coe_truncation_of_many_specializations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/BranchEvaluation.lean`:

```text
'AspisWide.BranchEvaluation.henselDenominatorExponent_le_of_lt' depends on axioms: [propext, Quot.sound]
'AspisWide.BranchEvaluation.integralBranchToFunctionField_clearedFiniteBranchEvaluation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.specialization_clearedFiniteBranchEvaluation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.sum_coeff_shiftedCandidateSeries_eq_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.specialization_clearedFiniteBranchDiscrepancy_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.finiteBranchValue_eq_received_of_discrepancy_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.candidate_eval_eq_received_of_discrepancy_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.integralBranchIteratedWeight_clearedFiniteBranchEvaluation_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.integralBranchIteratedWeight_sub_triple_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.integralBranchIteratedWeight_clearedFiniteBranchDiscrepancy_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.BranchEvaluation.finiteBranchValue_eq_received_of_many_agreements' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/AmbientCurve.lean`:

```text
'AspisWide.AmbientCurve.lagrangeAmbientCurve_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.AmbientCurve.lagrangeAmbientCurve_at_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.AmbientCurve.candidate_eval_eq_lagrangeAmbientCurve_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Cardinality.lean`:

```text
'AspisWide.Cardinality.card_fin_of_fintype' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Cardinality.card_fin_lt_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/FixedBranchCurve.lean`:

```text
'AspisWide.FixedBranchCurve.exists_ambient_curve_of_fixed_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/ReleasedLift.lean`:

```text
'AspisWide.ReleasedLift.releasedInterpolationComponents_curve_eq_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.ReleasedLift.exists_released_components_of_ambient_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.ReleasedLift.exists_exactInitial_components_of_ambient_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.ReleasedLift.exists_exactFinal_components_of_ambient_curve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/ConcreteBranch.lean`:

```text
'AspisWide.ConcreteBranch.exists_exactFinal_components_of_fixed_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.ConcreteBranch.exists_exactInitial_components_of_fixed_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/EncoderRegression.lean`:

```text
'AspisWide.EncoderRegression.initialEncoder_eq_v7' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.EncoderRegression.finalEncoder_eq_v7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/OuterSelection.lean`:

```text
'AspisWide.OuterSelection.zeroSpecializationChallengeSet_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.OuterSelection.sum_toFinset_le_multiset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.OuterSelection.sigma_card_le_of_local_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.OuterSelection.sigma_scaledBudget_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.OuterSelection.exists_weighted_fixed_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/FinalRoot.lean`:

```text
'AspisWide.Terminal.final_challengeCandidateHom_curveTrivariatePolynomial_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Terminal.exactFinal_challengeCandidateHom_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/FinalBranch.lean`:

```text
'AspisWide.Terminal.exists_exactV7Final_components_of_branchSelection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/FinalSelection.lean`:

```text
'AspisWide.Terminal.exists_exactV7Final_weighted_fixed_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/FinalCurveBranch.lean`:

```text
'AspisWide.Terminal.exists_exactV7Final_components_of_selected_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/FinalCurve.lean`:

```text
'AspisWide.Terminal.exists_exactV7Final_curve_of_interpolant' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Terminal.exists_exactV7Final_curve_of_valid_challenges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Terminal.lean`:

```text
'AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Terminal.exactV7FinalPublishedOneFoldCurveDecodability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/InitialRoot.lean`:

```text
'AspisWide.Terminal.challengeCandidateHom_curveTrivariatePolynomial_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Terminal.exactInitial_challengeCandidateHom_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/InitialBranch.lean`:

```text
'AspisWide.Terminal.exists_exactV7Initial_components_of_branchSelection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/InitialSelection.lean`:

```text
'AspisWide.Terminal.exists_exactV7Initial_weighted_fixed_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/InitialCurveBranch.lean`:

```text
'AspisWide.Terminal.exists_exactV7Initial_components_of_selected_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/InitialCurve.lean`:

```text
'AspisWide.Terminal.exists_exactV7Initial_curve_of_interpolant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Terminal.exists_exactV7Initial_curve_of_valid_challenges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`Wide/Initial.lean`:

```text
'AspisWide.Terminal.exactV7InitialWidth29CurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Terminal.exactV7InitialPublishedWidth29CurveDecodability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`WideTower.lean`:

```text
'AspisWideTower.qm31_wideU_not_isSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWideTower.wideExact_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWideTower.wideExact_natCast_ne_zero_of_pos_of_lt_characteristic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWideTower.wideExact_two_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWideTower.qm31_to_wide_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Wide/Instances.lean`:

```text
'AspisWide.Instances.wideInitialWidth29CurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Instances.wideFinalDegreeThreeCurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Instances.unchangedChallengeCaps' does not depend on any axioms
```

`Wide/Regression.lean`:

```text
'AspisWide.Regression.qm31InitialWidth29CurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Regression.qm31FinalDegreeThreeCurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Regression.initialResult_eq_v7' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Regression.finalResult_eq_v7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

</details>

### Part B1: heartbeat provenance

There are **25** `set_option maxHeartbeats` directives in the 47 committed
Wide files, including all ten identified in the replay request. Nineteen
have literal same-declaration counterparts in V7. Six attach to new final
helper declarations and are listed as **new**, even where their value matches
an Initial-helper analogue. No setting changed during this replay.

V7 paths in the table are relative to
`/Users/dominic/ZK/AspisFormal/AspisFormal/K1/`; Wide paths are relative to
this research directory’s `lean/`. Each quoted instruction is the exact
line at the cited location.

| Wide location | Exact instruction | V7 counterpart or finding |
|---|---|---|
| `Wide/Agreement.lean:105` | `set_option maxHeartbeats 1000000 in` | `V7ExactCorrelatedAgreement.lean:315` — identical line |
| `Wide/Agreement.lean:162` | `set_option maxHeartbeats 1000000 in` | `V7ExactCorrelatedAgreement.lean:372` — identical line |
| `Wide/BranchEvaluation.lean:16` | `set_option maxHeartbeats 2000000` | `V7ExactCorrelatedAgreementBranchEvaluation.lean:16` — identical line |
| `Wide/ConcreteBranch.lean:48` | `set_option maxHeartbeats 2000000 in` | `V7ExactCorrelatedAgreementConcreteBranch.lean:43` — identical line |
| `Wide/ConcreteBranch.lean:213` | `set_option maxHeartbeats 2000000 in` | `V7ExactCorrelatedAgreementConcreteBranch.lean:208` — identical line |
| `Wide/FinalBranch.lean:41` | `set_option maxHeartbeats 300000 in` | **New final declaration**; no same-declaration V7 counterpart. Initial analogue: `V7ExactCorrelatedAgreementInitialBranch.lean:37`, `set_option maxHeartbeats 1000000 in`. |
| `Wide/FinalCurve.lean:47` | `set_option maxHeartbeats 300000 in` | **New final declaration**; no same-declaration V7 counterpart. Initial analogue: `V7ExactCorrelatedAgreementInitialCurve.lean:43`, `set_option maxHeartbeats 300000 in`. |
| `Wide/FinalCurve.lean:89` | `set_option maxHeartbeats 300000 in` | **New final declaration**; no same-declaration V7 counterpart. Initial analogue: `V7ExactCorrelatedAgreementInitialCurve.lean:85`, `set_option maxHeartbeats 300000 in`. |
| `Wide/FinalCurveBranch.lean:44` | `set_option maxHeartbeats 300000 in` | **New final declaration**; no same-declaration V7 counterpart. Initial analogue: `V7ExactCorrelatedAgreementInitialCurveBranch.lean:39`, `set_option maxHeartbeats 300000 in`. |
| `Wide/FinalRoot.lean:62` | `set_option maxHeartbeats 300000 in` | **New final declaration**; no same-declaration V7 counterpart. Initial analogue: `V7ExactCorrelatedAgreementInitialRoot.lean:87`, `set_option maxHeartbeats 2000000 in`. |
| `Wide/FinalSelection.lean:39` | `set_option maxHeartbeats 300000 in` | **New final declaration**; no same-declaration V7 counterpart. Initial analogue: `V7ExactCorrelatedAgreementInitialSelection.lean:35`, `set_option maxHeartbeats 300000 in`. |
| `Wide/HenselSpecialization.lean:15` | `set_option maxHeartbeats 2000000` | `V7ExactCorrelatedAgreementHenselSpecialization.lean:15` — identical line |
| `Wide/Initial.lean:46` | `set_option maxHeartbeats 300000 in` | `V7ExactCorrelatedAgreementInitial.lean:42` — identical line |
| `Wide/InitialBranch.lean:41` | `set_option maxHeartbeats 1000000 in` | `V7ExactCorrelatedAgreementInitialBranch.lean:37` — identical line |
| `Wide/InitialCurve.lean:47` | `set_option maxHeartbeats 300000 in` | `V7ExactCorrelatedAgreementInitialCurve.lean:43` — identical line |
| `Wide/InitialCurve.lean:89` | `set_option maxHeartbeats 300000 in` | `V7ExactCorrelatedAgreementInitialCurve.lean:85` — identical line |
| `Wide/InitialCurveBranch.lean:44` | `set_option maxHeartbeats 300000 in` | `V7ExactCorrelatedAgreementInitialCurveBranch.lean:39` — identical line |
| `Wide/InitialRoot.lean:91` | `set_option maxHeartbeats 2000000 in` | `V7ExactCorrelatedAgreementInitialRoot.lean:87` — identical line |
| `Wide/InitialSelection.lean:39` | `set_option maxHeartbeats 300000 in` | `V7ExactCorrelatedAgreementInitialSelection.lean:35` — identical line |
| `Wide/MultiplicityThreeGS.lean:834` | `set_option maxHeartbeats 800000 in` | `V7Tag73ExactMultiplicityThreeGS.lean:830` — identical line |
| `Wide/MultiplicityThreeGS.lean:1016` | `set_option maxHeartbeats 800000 in` | `V7Tag73ExactMultiplicityThreeGS.lean:1012` — identical line |
| `Wide/OuterSelection.lean:234` | `set_option maxHeartbeats 2000000 in` | `V7ExactCorrelatedAgreementOuterSelection.lean:230` — identical line |
| `Wide/RegularWeights.lean:621` | `set_option maxHeartbeats 1000000 in` | `V7ExactCorrelatedAgreementRegularWeights.lean:617` — identical line |
| `Wide/Smooth.lean:306` | `set_option maxHeartbeats 1000000 in` | `V7ExactCorrelatedAgreementSmooth.lean:302` — identical line |
| `Wide/Terminal.lean:99` | `set_option maxHeartbeats 300000 in` | `V7ExactCorrelatedAgreementTerminal.lean:95` — identical line |

In particular, of the ten specifically requested directives, five have
literal V7 counterparts (HenselSpecialization, Initial, RegularWeights,
OuterSelection, Terminal), while five belong to the new FinalRoot,
FinalBranch, FinalCurveBranch and two FinalCurve declarations.
FinalSelection contributes the sixth new directive outside that ten-item
subset. The original monolithic final theorem had its own 300000 setting
at `V7ExactCorrelatedAgreementTerminal.lean:95`; that does not make every
new helper directive an inherited same-declaration line. The earlier log’s
explicit statement that the new final helpers use local 300000 settings is
accurate; any blanket interpretation that all settings were inherited is not.

### Part B2: normalized port diff

Read-only comparison of the 47 files in `docs/research/v8-wide-reference-20261005/lean/Wide/` against their V7 sources. Imports were omitted in normalized diffs; namespace redirects and `QM31Exact` → target field (`E` or `K`) were normalized. All 43 mapped modules add a generic field context: `{E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod AspisCircleGroupOrder.P) E]` (named `K` in the three encoder/GRS modules). Originally generic declarations keep their own binders; unused outer binders do not become premises. Tower namespace openings are removed or replaced by `open AspisCircleGroupOrder (P)`, and `M31Exact` is expanded to `ZMod P` where needed. No additional cardinality assumption is introduced. The normalized diffs were inspected against the sources and the successful Part A replay.

Artifacts are retained under the replay workspace’s `evidence/B2/`: `full-diffs/<Name>.diff` retains the whole normalized file comparison (including module setup, comments, attributes, and commands); `matched-diffs/<Name>.diff` compares same-named declaration bodies, with source and target line numbers in the headers. `declaration-inventory.tsv` records matching, changed, added, and source-only names per mapped file. Four port-only files have no source counterpart, so no diff is emitted for them. A zero-byte matched diff means the matched declarations are identical after normalization.

#### File-by-file declaration inventory

“Changed” below means a matched declaration has a textual statement/body difference after the allowed normalizations. Every other matched declaration in that file is text-identical. Full diff files also show non-declaration text and module-level settings.

| Wide file | V7 source | Matched declarations with differences |
|---|---|---|
| Agreement | `K1/V7ExactCorrelatedAgreement.lean` | `exactFinalValidCandidate_substitute_eq_zero`, `exactInitialNormalizedLanes`, `exactInitialValidCandidate_substitute_eq_zero`, `exists_exactFinalCurveInterpolation`, `exists_exactInitialCurveInterpolation` |
| AmbientCurve | `K1/V7ExactCorrelatedAgreementAmbientCurve.lean` | none |
| BranchEvaluation | `K1/V7ExactCorrelatedAgreementBranchEvaluation.lean` | none |
| Cardinality | new | — |
| ConcreteBranch | `K1/V7ExactCorrelatedAgreementConcreteBranch.lean` | `exists_exactFinal_components_of_fixed_branch`, `exists_exactInitial_components_of_fixed_branch` |
| EncoderLinearity | `K1/V7ExactCorrelatedAgreement.lean` | none |
| EncoderRegression | new | — |
| FactorBudgets | `K1/V7ExactCorrelatedAgreementFactorBudgets.lean` | none |
| Factors | `K1/V7ExactCorrelatedAgreementFactors.lean` | `trivariateCoefficient_natCast_ne_zero_of_pos_of_lt_characteristic` |
| FinalBranch | `K1/V7ExactCorrelatedAgreementTerminal.lean` | no same-named source declaration; see split-helper map below |
| FinalCurve | same Terminal source | no same-named source declaration; see split-helper map below |
| FinalCurveBranch | same Terminal source | no same-named source declaration; see split-helper map below |
| FinalEncoder | `K1/V7Tag73ExactOneFoldEncoderBinding.lean` | `exactFinalEncoder_injective`, `exactFinalEvaluationIdentity`, `exactInitialEncoder_eq_circleLift` |
| FinalRoot | same Terminal source | no same-named source declaration; see split-helper map below |
| FinalSelection | same Terminal source | no same-named source declaration; see split-helper map below |
| FiniteBranch | `K1/V7ExactCorrelatedAgreementFiniteBranch.lean` | none |
| FixedBranchCurve | `K1/V7ExactCorrelatedAgreementFixedBranchCurve.lean` | none |
| FunctionField | `K1/V7ExactCorrelatedAgreementFunctionField.lean` | `bivariateCoefficient_natCast_ne_zero_of_pos_of_lt_characteristic` |
| GRSConversion | `K1/V7Tag73ExactGRSConversion.lean` | `exactCircleDenominator_ne_zero`, `exactCircleGRSMultiplier_ne_zero`, `exactCircleGRSPoint`, `exactCircleGRSPoint_injective`, `exactCircleGRSPolynomial`, `exactCircleGRSPolynomial_injective`, `exactFinalGRSConversion`, `exactFinalMessagePolynomial_complete`, `exactInitialEncoder_coordinate_grs`, `exactInitialGRSConversion` |
| Hensel | `K1/V7ExactCorrelatedAgreementHensel.lean` | none |
| HenselCombinatorics | `K1/V7ExactCorrelatedAgreementHenselCombinatorics.lean` | none |
| HenselIntegralLift | `K1/V7ExactCorrelatedAgreementHenselIntegralLift.lean` | none |
| HenselRecurrence | `K1/V7ExactCorrelatedAgreementHenselRecurrence.lean` | none |
| HenselSpecialization | `K1/V7ExactCorrelatedAgreementHenselSpecialization.lean` | none |
| HenselWeights | `K1/V7ExactCorrelatedAgreementHenselWeights.lean` | `nonsaturatedLinearBranch_generator_ceiling_ne_leading_add_one`, `nonsaturatedLinearBranch_irreducible`, `nonsaturatedLinearBranch_iteratedWeight`, `nonsaturatedLinearBranch_monic` |
| Initial | `K1/V7ExactCorrelatedAgreementInitial.lean` | `exactV7InitialPublishedWidth29CurveDecodability`, `exactV7InitialWidth29CurveDecodable` |
| InitialBranch | `K1/V7ExactCorrelatedAgreementInitialBranch.lean` | `exists_exactV7Initial_components_of_branchSelection` |
| InitialCurve | `K1/V7ExactCorrelatedAgreementInitialCurve.lean` | `exists_exactV7Initial_curve_of_interpolant` |
| InitialCurveBranch | `K1/V7ExactCorrelatedAgreementInitialCurveBranch.lean` | `exists_exactV7Initial_components_of_selected_branch` |
| InitialEncoder | `Pool/V7C1ConcreteProjectionBinding.lean` | `exactInitialEncoder`, `exactInitialEncoderCircleRealization` |
| InitialRoot | `K1/V7ExactCorrelatedAgreementInitialRoot.lean` | `exactInitial_challengeCandidateHom_eq_zero` |
| InitialSelection | `K1/V7ExactCorrelatedAgreementInitialSelection.lean` | `exists_exactV7Initial_weighted_fixed_branch` |
| Instances | new | — |
| Interpolation | `K1/V7ExactCorrelatedAgreementInterpolation.lean` | none |
| LocalFactors | `K1/V7ExactCorrelatedAgreementLocalFactors.lean` | none |
| MultiplicityThreeGS | `K1/V7Tag73ExactMultiplicityThreeGS.lean` | explicit field arguments on the conversion, interpolation, candidate, decoder and boundary declarations; encoder namespace redirects and `M31Exact` → `ZMod P` in `qm31ExactTwoNeZero` (complete names below) |
| OuterSelection | `K1/V7ExactCorrelatedAgreementOuterSelection.lean` | none |
| PowerSeriesLift | `K1/V7ExactCorrelatedAgreementPowerSeriesLift.lean` | none |
| Regression | new | — |
| RegularEvaluation | `K1/V7ExactCorrelatedAgreementRegularEvaluation.lean` | none |
| RegularHensel | `K1/V7ExactCorrelatedAgreementRegularHensel.lean` | none |
| RegularRing | `K1/V7ExactCorrelatedAgreementRegularRing.lean` | none |
| RegularWeights | `K1/V7ExactCorrelatedAgreementRegularWeights.lean` | none |
| RegularZeroCount | `K1/V7ExactCorrelatedAgreementRegularZeroCount.lean` | none |
| ReleasedLift | `K1/V7ExactCorrelatedAgreementReleasedLift.lean` | none |
| Smooth | `K1/V7ExactCorrelatedAgreementSmooth.lean` | `exists_exactV7_uniformSmoothEvaluationPoint` |
| Terminal | `K1/V7ExactCorrelatedAgreementTerminal.lean` | `exactV7FinalDegreeThreeCurveDecodable`, `exactV7FinalPublishedOneFoldCurveDecodability` |

#### Difference details

The matched differences in Agreement, ConcreteBranch, FinalEncoder, HenselWeights, Initial, InitialBranch, InitialCurve, InitialRoot, InitialSelection, and most MultiplicityThreeGS declarations are explicit `(K := E)` / `(K := K)` applications for field-generic structures and definitions. These changes make field instantiations explicit. FinalEncoder also expands the base-field alias in the injectivity proof. In MultiplicityThreeGS, all 25 changed entries are field-parameter applications and redirected references to the generic encoders; the exact per-declaration text is in its diff.

Factors and FunctionField replace the hard-coded `qm31Exact_natCast_ne_zero_of_pos_of_lt_characteristic` call with the port’s generic `field_natCast_ne_zero_of_pos_of_lt_characteristic (E := E)` call. The field-specific source helper is correspondingly replaced by a generic helper declaration.

The non-mechanical matched proof changes are:

- `GRSConversion.lean`: the point denominator proof uses `ZMod P` as its parameter domain and changes the injectivity/map-zero step (source declaration at line 144; target declaration at line 128). `exactCircleGRSPolynomial_eq_released` changes from `rfl` to a `simp only` proof (target line 106), and `exactFinalMessagePolynomial_complete` adds an explicit `n := 256` and unfolds the generic conversion (source line 90; target line 72). The source-specific `qm31Exact_two_ne_zero` helper is replaced by `m31_neg_one_not_isSquare` over `ZMod P` (target lines 19–22); generic odd-characteristic facts come from the ported encoder.
- `InitialEncoder.lean`: the evaluator body is unchanged after field substitution; its apparent matched diff is only a trailing source comment. The circle realization makes `(K := K)` explicit (source declaration at line 237; target at line 57). The generic `two_ne_zero` lemma and exported `neZeroTwo` instance replace the source’s private theorem/local instance. Source projection and decoder packaging are omitted as listed below.
- `InitialCurveBranch.lean`: the selected-cardinality proof replaces `rw [Fintype.card_fin]; omega` with `AspisWide.Cardinality.card_fin_lt_of_budget`, supplying explicit dimension, degree, budget, and count (source proof at lines 86–89; target proof at lines 90–100).
- `Smooth.lean`: the smooth evaluation-point proof replaces the fixed `qm31Exact_card` rewrite with the generic lower bound `P ≤ Fintype.card E` proved using injectivity of the base-field algebra map (source declaration at line 499, old cardinality step at line 538; target declaration at line 503, new lower bound at line 542).
- `Terminal.lean`: final decodability now calls `exists_exactV7Final_curve_of_valid_challenges` after the same good-challenge packaging and outer-count steps; published-interface statement applications are explicit in `E` (source lines 99–209; target lines 103–134).

There are four port-only modules: `Cardinality.lean` adds `card_fin_of_fintype` and `card_fin_lt_of_budget`; `EncoderRegression.lean` adds `initialEncoder_eq_v7` and `finalEncoder_eq_v7`; `Instances.lean` adds `wideInitialWidth29CurveDecodable`, `wideFinalDegreeThreeCurveDecodable`, and `unchangedChallengeCaps`; `Regression.lean` adds `qm31InitialWidth29CurveDecodable`, `qm31FinalDegreeThreeCurveDecodable`, `initialResult_eq_v7`, and `finalResult_eq_v7`.

`EncoderLinearity.lean` adds `exactInitialEncoder_injective` (target line 221), proved from the existing overlap cap. Its other declaration blocks are split from the original Agreement module into `Agreement.lean` and `EncoderLinearity.lean`; the source-only declaration names reported per file are relocations, not removals. `Factors.lean` adds the generic field helper `field_natCast_ne_zero_of_pos_of_lt_characteristic` (target line 469). `GRSConversion.lean` adds `m31_neg_one_not_isSquare` (target line 19) and drops the source-only `qm31Exact_two_ne_zero` theorem and `qm31ExactNeZeroTwo` local instance; the generic encoder module supplies the field-level `two_ne_zero` fact used by the port.

Four source declarations are not carried into `FinalEncoder.lean`: `ExactOneFoldInverseTables`, `exactOneFoldAlgebraBinding`, `qm31ExactNeZeroTwo`, and `qm31ExactTwoNeZero` (source-only names in declaration-inventory.tsv). The field-specific nonzero-2 support is replaced by the generic encoder lemma; the inverse-table declarations are excluded by the target module comment. `InitialEncoder.lean` omits source projection/transcript packaging declarations in `Pool/V7C1ConcreteProjectionBinding.lean`: `projectBaseAddHom` (line 76), `doubledFactor_algebraMap` (106), `naturalLineValue_algebraMap` (117), `projectBase_naturalCoefficientPolynomial_eval` (131), `projectBase_initialP0_eval` (157), `projectBase_initialP1_eval` (177), `exactInitialEncoder_commutes` (213), and `initialProjectionBinding_of_initialEncoder_eq` (278); it carries the evaluator and distance facts selected for the generic encoder module. The source scanner’s `needed` entry is comment text, not a declaration, and is excluded from this list. InitialEncoder also replaces the source’s `qm31Exact_two_ne_zero` and `qm31ExactNeZeroTwo`; Agreement/EncoderLinearity omit the duplicate `qm31ExactTwoNeZero` and `qm31ExactNeZeroTwo` in favor of the imported generic instance.

#### Final helper split from the monolithic source Terminal

These are new declaration names extracted from proof blocks inside source `K1/V7ExactCorrelatedAgreementTerminal.lean`’s `exactV7FinalDegreeThreeCurveDecodable` theorem. Source references are line numbers in that original theorem; target references identify each helper.

| Added declaration | Target location | Corresponding source block |
|---|---|---|
| `final_challengeCandidateHom_curveTrivariatePolynomial_eq_zero` | `FinalRoot.lean:42` | Candidate-root construction at source lines 116–134 |
| `exactFinal_challengeCandidateHom_eq_zero` | `FinalRoot.lean:67` | Same candidate-root construction, packaged as the helper theorem |
| `exists_exactV7Final_weighted_fixed_branch` | `FinalSelection.lean:42` | Weighted fixed-branch selection at source lines 144–161 |
| `exists_exactV7Final_components_of_branchSelection` | `FinalBranch.lean:44` | Selected-branch Hensel and component lift at source lines 162–195 |
| `exists_strengthen` | `FinalCurveBranch.lean:36` | Existential/cardinality strengthening used after selected-branch extraction; source lines 196–203 provide the original existential assembly |
| `exists_exactV7Final_components_of_selected_branch` | `FinalCurveBranch.lean:47` | Selected tuple extraction and branch-to-components assembly at source lines 162–203 |
| `exists_four_elim` | `FinalCurve.lean:39` | Generic four-witness elimination helper; the original proof used direct `obtain`/`refine` around source lines 144–203 |
| `exists_exactV7Final_curve_of_interpolant` | `FinalCurve.lean:51` | Interpolation, root selection, and component assembly in source lines 107–203 |
| `exists_exactV7Final_curve_of_valid_challenges` | `FinalCurve.lean:94` | Source lines 107–203, with interpolation packaged into the preceding helper |

The source’s final public theorem remains in `Terminal.lean`; its body delegates through these extracted helpers. This mapping is structural correspondence, not a judgment about proof premises.

#### Options and audit commands

The per-file full diffs retain every option and command. All files retain `autoImplicit false`. The separate heartbeat inventory records all 25 heartbeat directives. Other observed option deltas are: the two source Agreement heartbeat scopes leave `EncoderLinearity` as their declarations are separated; `FinalEncoder` drops module `maxRecDepth 100000` and `maxHeartbeats 1000000`; `GRSConversion` drops module `maxRecDepth 100000`; `FinalBranch`, `FinalCurveBranch`, `FinalRoot`, and `FinalSelection` omit source Terminal’s scoped `linter.constructorNameAsVariable false`; `FinalCurve` adds a second scoped `maxRecDepth 1048576` / `maxHeartbeats 300000` pair for its second extracted theorem. The split modules add `#print axioms` commands for extracted declarations; those are visible in the full diffs.

The generic GRS source currently has no `maxRecDepth` override. The earlier failed-attempt narrative about locally retaining that option does not describe the final committed file; the final file passed this replay at the default recursion setting.

The exact changed MultiplicityThreeGS declarations are: `ExactInitialCloseCandidate`, `exactFinalAmbientDegreeConvention`, `exactFinalCloseCandidate_substitute_eq_zero`, `exactFinalDecodedCandidates`, `exactFinalInterpolationCoefficients_kernel`, `exactFinalMultiplicityThreeGS`, `exactFinalPolynomialAgreement_card_eq`, `exactFinalRootCandidates`, `exactFinalRootCandidates_mem_iff`, `exactInitialAmbientDegreeConvention`, `exactInitialCloseCandidate_card_lt_101`, `exactInitialCloseCandidate_substitute_eq_zero`, `exactInitialCloseCandidates`, `exactInitialDecodedCandidates`, `exactInitialGSDecode_mem_iff`, `exactInitialInterpolationCoefficients_kernel`, `exactInitialMultiplicityThreeGS`, `exactInitialNormalizedReceived`, `exactInitialPolynomialAgreement_card_eq`, `exactInitialRootCandidates`, `exactInitialRootCandidates_complete`, `exactInitialRootCandidates_mem_iff`, `exists_exactFinalInterpolation`, `exists_exactInitialInterpolation`, `qm31ExactTwoNeZero`.

### Part B3: statement identity, not only proof irrelevance

The exact type of both
`AspisWide.Regression.qm31InitialWidth29CurveDecodable` and
`AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7InitialWidth29CurveDecodable`
is:

```lean
AspisV6Width29CorrelatedAgreement.Width29CurveDecodable
  AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
  38229 AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap
```

The exact type of both
`AspisWide.Regression.qm31FinalDegreeThreeCurveDecodable` and
`AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7FinalDegreeThreeCurveDecodable`
is:

```lean
AspisV5FriDegreeThreeCorrelatedAgreement.DegreeThreeCurveDecodable
  AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
  9557 AspisV6PublishedTheoremInterfaces.foldChallengeCap
```

The replayed `EncoderRegression` theorems prove equality of the generic QM31
encoders with the V7 encoders by `rfl`. After unfolding those encoder
equalities, the statement types are syntactically identical. More strongly,
the two closed `Regression` declarations already use the V7 encoder names:
a scratch compiler command compared their actual environment `Expr` types
with those of the original declarations using `==`, and both comparisons
returned true. It printed both types with `pp.fullNames=true`.

The same scratch target kernel-checked proposition equalities between the
generic-QM31 and original V7 statement types by `rfl`. Both axiom outputs were
`[propext, Classical.choice, Quot.sound]`. Thus the original proof-term
identities by `Subsingleton.elim` are accompanied by a direct statement check;
proof irrelevance alone is not being used to infer a semantic match.

| Scratch audit | SHA-256 | Exit | Wall | Peak RSS KiB | Swaps | Axioms |
|---|---|---:|---|---:|---:|---|
| `B-StatementAudit` | `28c0e635e51b0f5778b4fc4ad888742fc9f55a5ec96446f6988f445e23a7539e` | 1 | 0:02.85 | 6867728 | 0 | Failed target; not proof evidence |
| `B-StatementAudit-02` | `5ab2ae4059ed4fe6a4cab7972f9e2e2ba83c6f71d012fce5836fee01e5fd9bf3` | 0 | 0:02.95 | 6904520 | 0 | Two reports, PCQ only |

Both use the replayed Wide objects, the same dependency set and the fixed
`-M7000`/7 GiB setting. Scratch source and output are external evidence only.

Part B is complete: all normalized changes are accounted for; the six new
helper heartbeat directives are explicitly distinguished; endpoint types and
encoder identities are checked. No original source, theorem statement,
threshold, cap or heartbeat setting was changed in this replay.

### Part C: Phase 5

Parts A and B were completed before Phase 5 source work began. All six new
modules below compile from source at the same measured `-M7000` setting,
with `-j1 -DElab.async=false`, one 7 GiB no-swap scope at a time, and the same
search path and pinned dependency sets. No original Wide source was edited.
The new sources use the default heartbeat setting. All cardinality and
root-count arguments are symbolic; no challenge field is enumerated.

#### C1: matched degree-three response bound

`AspisWide.DegreeThreeMatched.degreeThree_bad_response_challenges_card_le`
is generic over a finite field, finite domain and arbitrary message type.
Its sole decodability premise is
`DegreeThreeCurveDecodable encoder agreementThreshold challengeThreshold`.
`BadResponse` means a valid response for which there is no tuple of four
messages whose joint agreement contains the response support and whose
encoded curve equals the response candidate. `badStrategy` retains the
original candidate and masks every other support to the empty set.

The proof follows `width29_bad_response_challenges_card_le`: if there were
more than `challengeThreshold` bad challenges, apply curve decodability to
the masked strategy, choose a selected challenge outside the resolving
roots, and use `support_subset_jointAgreement` to obtain a matching tuple,
contradicting badness. `mem_badStrategy_good_iff` identifies the counted set
exactly with the original strategy's bad responses. All challenges,
including zero, are counted in this degree-three formulation.

`AspisWide.MatchedInstances.final_matchingDecomposition_iff` proves that,
for the injective linear exact final encoder, the encoded-curve condition
is equivalent to the candidate message being
`exactFinalMessageCurve components z`.
`exactFinal_bad_response_challenges_card_le` applies the replayed generic
terminal theorem with strict agreement threshold **9557** (at least 9558
points) and the unchanged `foldChallengeCap` **9396508281246**.
`wideFinal_bad_response_challenges_card_le` instantiates it at `WideExact`.

#### C2: joint list of 29 codewords

The prerequisite was located before constructing the new proof:
`AspisWide.MultiplicityThreeGS.exactInitialCloseCandidate_card_lt_101`
(`lean/Wide/MultiplicityThreeGS.lean:1134`), ported from
`AspisK1.V7Tag73ExactMultiplicityThreeGS.exactInitialCloseCandidate_card_lt_101`
(`AspisFormal/AspisFormal/K1/V7Tag73ExactMultiplicityThreeGS.lean:1130`).
It was compiled from source in Part A and states:

```lean
Nat.card (ExactInitialCloseCandidate received) < 101
```

Here `ExactInitialCloseCandidate received` consists of initial messages
whose exact encoded words agree with `received` on at least **38230**
points. This supplies the usable theorem for F3, rather than an audit-only
reference.

`AspisWide.BatchSeparation.exists_nonzero_injective_batch` separates a
finite family of 29-tuples whenever
`family.card.choose 2 * 28 < Fintype.card K - 1`. For each unordered pair,
one differing coordinate gives a nonzero polynomial of degree at most 28;
`width29_nonzero_collision_card_le` bounds its nonzero roots. The union
has at most `choose(card family,2)*28` elements. For 101 tuples this is
**141400**, and the prime-field embedding already gives enough nonzero
challenges; no extra size premise is added to the joint-list theorem.

`AspisWide.JointList.jointInitialList_card_le_100` batches a chosen
101-element subfamily of message tuples with this challenge. Linearity
preserves their joint 38230-point agreements with the batched received
word. Injective batching would produce 101 distinct single-word close
candidates, contradicting the located theorem.

The literal codeword-tuple form is
`AspisWide.JointList.jointInitialCodewords_card_le_100`. Its statement, with
`{K : Type} [Field K] [Fintype K] [DecidableEq K]`
and `[Algebra (ZMod AspisCircleGroupOrder.P) K]`, is:

```lean
(lanes : Fin 29 → InitialWord K)
(family : Finset (Fin 29 → InitialWord K))
(codewords : ∀ words ∈ family, ∀ i,
  ∃ message : InitialMessage K, exactInitialEncoder message = words i)
(close : ∀ words ∈ family,
  38230 ≤ (Finset.univ.filter fun x => ∀ i, lanes i x = words i x).card) :
family.card ≤ 100
```

`wideJointInitialList_card_le_100` and
`wideJointInitialCodewords_card_le_100` instantiate both forms at WideExact.
The given words are arbitrary, so the same theorem covers either list in
R0 §5 step 1 when its words are supplied. This does not establish the
remaining steps of that paper argument.

#### C3: subfield descent by conjugation and distance

The prerequisite distance theorem was located and replayed in Part A:
`AspisWide.InitialEncoder.exactInitialEncoder_overlap_cap`
(`lean/Wide/InitialEncoder.lean:74`). Distinct initial messages have exact
codewords agreeing on at most **1024** points; it applies the existing
`AspisV5FriCircleEncoderDistance.agreementSet_card_le_1024` theorem to the
exact stored circle realization.

`AspisWide.EncoderConjugation.map_initialEncoder` proves that every ring
endomorphism of K commutes with the exact initial encoder. The proof first
commutes the doubled-factor recurrence, natural-basis products and
coefficient-polynomial evaluation. Every such map fixes `ZMod P`, by
uniqueness of its ring homomorphism into K, so it fixes the stored
coordinates. This verifies the needed encoder symmetry directly.

`initialMessage_fixed_of_agreement` applies the distance bound: if a
conjugation fixes the received word, a conjugated codeword and the original
codeword agree throughout the given support. More than 1024 such points
forces the conjugated message to equal the original.
`initialCodeword_descends` then uses Mathlib's
`IsGalois.mem_range_algebraMap_iff_fixed` for an arbitrary field F embedded
in K. Finite dimensionality and the Galois instance follow from K being a
finite field; neither is an added theorem premise.

The subfield form
`AspisWide.SubfieldDescent.initialCodeword_subfield_descent`, under the
same generic field context as the joint-list theorem, is:

```lean
(S : Subfield K) (received : InitialWord K) (message : InitialMessage K)
(support : Finset (Fin 1048576)) (large : 1024 < support.card)
(agrees : ∀ x ∈ support, exactInitialEncoder message x = received x)
(subfieldValued : ∀ x, received x ∈ S) :
∀ x, exactInitialEncoder message x ∈ S
```

`wideInitialCodeword_subfield_descent` instantiates this result for every
subfield of WideExact. The conclusion concerns the entire exact initial
codeword, not merely its agreeing coordinates.

#### Phase 5 compile and axiom evidence

The source revision is `1aa58a9e9dac2c9c9cc6b6b09998e4a38d25a2c4` plus the
six added source files identified by their full hashes below. Those exact
bytes are the final Lean sources in this replay commit. The scratch
`Phase5Audit.lean` imports all three results together, the original
instances, and both regression modules. It adds no theorem or assumption.
Its successful final check is an integration audit for the new modules;
the unchanged 48-file replay was not repeated.

For the first six rows, paths are relative to `lean/`; the last row is
external scratch. Tags are the corresponding `evidence/<tag>.json` stems.
All rows have zero cgroup swap peak and zero OOM events. PCQ means only
`propext`, `Classical.choice`, `Quot.sound` (or a subset).

| Target | Tag | SHA-256 | Exit | Wall | Peak RSS KiB | Swaps | Axiom reports |
|---|---|---|---:|---|---:|---:|---|
| `Wide/DegreeThreeMatched.lean` | `C1-DegreeThreeMatched-01` | `3e89ec947768d5302138199238791a6fb7028183dc2037c45eb898175a069cd8` | 0 | 0:02.96 | 6718644 | 0 | 2, PCQ only |
| `Wide/MatchedInstances.lean` | `C1-MatchedInstances-01` | `6e9e16b392db18fe60d8f9fa3abbf11f0472c698d3f1f3fb7033933d8babb376` | 0 | 0:03.07 | 6763680 | 0 | 3, PCQ only |
| `Wide/BatchSeparation.lean` | `C2-BatchSeparation-02` | `55c39326ad6d1952a127f67138bf3d67c11a4d49b2b5b2c2aea10f24c15649f5` | 0 | 0:03.09 | 6728308 | 0 | 2, PCQ only |
| `Wide/JointList.lean` | `C2-JointList-02` | `762657e7cb378837efb33304ad5bfbc4849a152fe19358e8eb706edcdf894066` | 0 | 0:03.51 | 6758536 | 0 | 5, PCQ only |
| `Wide/EncoderConjugation.lean` | `C3-EncoderConjugation-01` | `6132a51edc5fd82194037416bfe2c2d4b8114d3125630ee9a822ef3a25686ee1` | 0 | 0:03.27 | 6736948 | 0 | 5, PCQ only |
| `Wide/SubfieldDescent.lean` | `C3-SubfieldDescent-02` | `118fbd048cc9f3ec02efbab9a35732e4b4aa6dcfadc0e87daf284ee9eecac697` | 0 | 0:03.46 | 6748772 | 0 | 4, PCQ only |
| `Phase5Audit.lean` | `C-Phase5Audit` | `167e18e373ede279a7c3da2ca3076a1ce0691db32d7b07a8064e6142361423f5` | 0 | 0:02.73 | 6871988 | 0 | 13, PCQ only |

The six new source files produce 21 clean reports. Literal axiom output:

```text
C1-DegreeThreeMatched-01
'AspisWide.DegreeThreeMatched.mem_badStrategy_good_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.DegreeThreeMatched.degreeThree_bad_response_challenges_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

C1-MatchedInstances-01
'AspisWide.MatchedInstances.final_matchingDecomposition_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.MatchedInstances.exactFinal_bad_response_challenges_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MatchedInstances.wideFinal_bad_response_challenges_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

C2-BatchSeparation-02
'AspisWide.BatchSeparation.pairCollisions_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.BatchSeparation.exists_nonzero_injective_batch' depends on axioms: [propext, Classical.choice, Quot.sound]

C2-JointList-02
'AspisWide.JointList.jointInitialCodewords_card_le_100' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.JointList.wideJointInitialCodewords_card_le_100' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.JointList.initialMessageCurve_eq_batch' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.JointList.jointInitialList_card_le_100' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.JointList.wideJointInitialList_card_le_100' depends on axioms: [propext, Classical.choice, Quot.sound]

C3-EncoderConjugation-01
'AspisWide.EncoderConjugation.map_doubledFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.EncoderConjugation.map_naturalLineValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.EncoderConjugation.map_naturalCoefficientPolynomial_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.EncoderConjugation.map_primeField' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.EncoderConjugation.map_initialEncoder' depends on axioms: [propext, Classical.choice, Quot.sound]

C3-SubfieldDescent-02
'AspisWide.SubfieldDescent.initialMessage_fixed_of_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.SubfieldDescent.initialCodeword_descends' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.SubfieldDescent.initialCodeword_subfield_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.SubfieldDescent.wideInitialCodeword_subfield_descent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

C-Phase5Audit
'AspisWide.DegreeThreeMatched.degreeThree_bad_response_challenges_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.MatchedInstances.wideFinal_bad_response_challenges_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.JointList.jointInitialCodewords_card_le_100' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.JointList.wideJointInitialCodewords_card_le_100' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.SubfieldDescent.initialCodeword_subfield_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.SubfieldDescent.wideInitialCodeword_subfield_descent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AspisWide.Instances.wideInitialWidth29CurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Instances.wideFinalDegreeThreeCurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Instances.unchangedChallengeCaps' does not depend on any axioms
'AspisWide.Regression.qm31InitialWidth29CurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.Regression.qm31FinalDegreeThreeCurveDecodable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.EncoderRegression.initialEncoder_eq_v7' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisWide.EncoderRegression.finalEncoder_eq_v7' depends on axioms: [propext, Classical.choice, Quot.sound]

```

### Failed attempts during this replay

Each failing compiler invocation stopped before the next target. None was
a memory failure, and no cap or existing theorem statement was changed.
The failed output is retained but is not proof evidence; any `sorryAx`
printed after an elaboration error is Lean's error recovery, not an admitted
source theorem. The final sources contain no `sorry`, `axiom` declaration,
or `native_decide`.

- `B-StatementAudit` — SHA-256 `28c0e635e51b0f5778b4fc4ad888742fc9f55a5ec96446f6988f445e23a7539e`; exit 1; wall 0:02.85; peak RSS 6867728 KiB; swaps 0; Scratch command used unqualified `logInfo`; changed it to `Lean.logInfo`, then `B-StatementAudit-02` passed.
- `C2-BatchSeparation-01` — SHA-256 `fda78ff899891219dae0533f9201794f0ed54503881630245d3d21e7ee9ab07e`; exit 1; wall 0:02.96; peak RSS 6694692 KiB; swaps 0; `unfold width29CurveValue` also targeted a goal without that constant; replaced it with `simp only [width29CurveValue, width29Batch]` at the hypothesis and goal, and replaced deprecated `push_neg` with `push Not`; unchanged statement passed as `C2-BatchSeparation-02`.
- `C2-JointList-01` — SHA-256 `5e339c9ce04bf33bcc99e28e6795834c99682c2111d4456faaad8666b07dd769`; exit 1; wall 0:03.15; peak RSS 6724688 KiB; swaps 0; Two redundant tactic tails ran after `simp only` and `rw [Nat.choose_two_right]` had closed their goals; removed the unused `sum_congr`/`mul_comm` and `norm_num` steps. Added the requested literal codeword-tuple wrappers; `C2-JointList-02` passed.
- `C3-SubfieldDescent-01` — SHA-256 `93da391e347327e8e2e9604a765384b4014266c87bfdca682db6387a343c3dab`; exit 1; wall 0:03.06; peak RSS 6716736 KiB; swaps 0; Rewriting under an unreduced lambda missed the left-side received value; inserted an explicit `change` after `map_initialEncoder` to expose the application. The same statements passed as `C3-SubfieldDescent-02`.

Part A had no failing source targets and required no proof diff. The
independent pre-replay `-M4500` import failures reported in the task are
historical input to this investigation, not additional attempts made here.

### Replay conclusion and limits

- **Part A complete:** all 47 committed Wide files plus WideTower compiled
  from source in the fresh object directory, with 303 clean axiom reports,
  at the import-measured `-M7000` / 7 GiB no-swap setting.
- **Part B complete:** all 47 source comparisons are accounted for; of 25
  heartbeat directives, 19 have literal V7 counterparts and six are new
  final-helper settings. Both QM31 endpoint statement types match V7
  syntactically, with the encoder identities checked by `rfl`.
- **Part C complete:** the generic matched degree-three bound, 100-tuple
  joint-list bound at 38230 points, and subfield descent above 1024 points
  are proved from source, including WideExact instances, with clean audits.
- The historical successful `-M4500` footprint remains unexplained. The
  measured replay setting and object-set hashes provide a reproducible
  successful source result without claiming a cause for that discrepancy.
- The R0 paper proof remains **unreviewed and unestablished as a whole**.
  No Fiat–Shamir theorem, semantic-layer bound, privacy result, source-to-R0
  correspondence, or full 100-bit soundness result is established here.
  No protocol, parameter, Rust, SBF, CU, frozen V7 or other research change
  was made. The earlier Phase 4 checkpoint status is historical and is
  superseded only by the specific source results recorded in this section.

## R0 structural audit and stop finding 2026-10-06

Source revision: `baa76e94ca718c22e1a648b8601b3a6d71a873cd` plus the four
new `lean/R0/` sources with exact hashes below. Branch:
`research/v8-wide-reference-20261005`; worktree:
`/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922`.
The final local source hashes match the compiled build-host bytes.

**Outcome: F4 proved from source; the requested stop condition is reached
at F5/(V2), in the §5 proof's comparison after step 6.** The paper never
defines `DualFold`. The cited `AspisR19.R370KernelEvaluation.dualFold` is
unscaled, whereas `kernel_eval_pairing` includes a factor `quarter` outside
the pairing. With the source quarter `4⁻¹` and `q=w=e₀`, for every alpha:

```text
P_{q,w}(alpha) = 1/4
<firstFold(alpha,q), cited dualFold(alpha,w)> = 1
1/4 != 1, including over WideExact
```

This is a missing normalisation specification; with the cited unscaled
meaning, F5's displayed evaluation equality is false. It is not a proof
that every possible meaning of the unspecified `DualFold` fails.
The exact blocked inference is “By (V2) and F5” before using exclusion
from B7. `comparison_step_counterexample` exhibits claimed polynomial `1`
and claim-prime `4`: the local unscaled (V2) and `c0+c4=claim-prime/4` hold,
but the evaluation equality with the source polynomial fails at every
alpha. This is a counterexample to that inference, not a complete accepting
R0 transcript or a cryptographic attack.

The smallest specification addition making this comparison provable is
`DualFold := (1/4) * cited dualFold`. If the unscaled dual is intended,
(V2) instead needs the factor `1/4`. Neither change was made. No premise,
threshold, cap, list size, or bad set was changed to accommodate the issue.
R0_SOUNDNESS.md retains the argument and records gap 13 and a §5 status line.

`AspisR0.Fold.F4` / `wideF4` package the exact encoded-channel identity,
fold commutation, and both inverses of the fibre transform. Fibres use
`childIndex u s` in order `(x,y),(x,-y),(-x,-y),(-x,y)`. Nonzero coordinates
follow from injectivity of the stored four domain points; inverse-table
correctness is not assumed. The exact encoders' existing circle-lift
identity supplies the basis correspondence directly.

`AspisR0.RoundNormalization.cited_round_identities` proves the degree bound
at most six, the quarter-scaled evaluation identity, and the exact
`c0+c4=(1/4)*dot(q,w)` boundary for the explicit source coefficient formula.
`wide_cited_round_identities` instantiates it at WideExact.
`unscaled_F5_counterexample` / `wide_unscaled_F5_counterexample` prove the
witness above. Independently, `AspisR0.CitedKernelAudit.literal_cited_kernel`
and `literal_cited_counterexample` apply the actual imported R370 theorem
and constants to the same impulse, with an arbitrary quarter (and, for the
inequality, the explicit condition `quarter != 1`). The Wide theorem proves
that condition for `4⁻¹`; it is not a new premise on R0.

F5 is not marked proved. F6 was not completed or refuted. The seven bad-set
definitions/bounds, binding theorem, and step-7 sampler theorem were not
implemented after this stop; no new Part B constants or sampler-law import
claim is made. Gaps 1, 2, and 5 are marked closed by the prior replay's named
results, and gap 4 only partly closed by F4. SEM, FS, privacy, and §6's state
function remain outside this work. R0 remains unreviewed and unestablished.

Environment: build host `dombarker@100.108.41.90`, separate workspace
`/home/dombarker/project-offloads/aspis-r0-20261006`; Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, binary SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`;
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
Read-only project objects are merged by symlinks in `cache/`: pinned V7
from `aspis-wide-replay-20261006/pinned-v7` first, replayed Wide objects
second, then `aspis-r126-release-20260930-a/lib`, keeping earlier duplicates.
Package paths are the replay's ordered Cli, batteries, Qq, aesop,
proofwidgets, importGraph, LeanSearchClient, plausible, mathlib, and Lean
library paths. `objects/` precedes `cache/`. The exact environment is retained
in `evidence/environment.json`; `evidence/lake-env-path.txt` records Lake's
additional empty local build path and toolchain prefix. No cache source or
object was edited, and no `lake build` or dependency build ran.

Import footprints (GNU time, no `-M`, each in the same capped scope):

| Import-only target | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Wide.FinalEncoder + WideTower | 0 | 2.70 s | 6710836 | 0 |
| Wide.MatchedInstances + Wide.JointList + Wide.SubfieldDescent | 0 | 2.71 s | 6728872 | 0 |
| AspisV8R19.R370KernelEvaluation alone | 0 | 0.96 s | 2336044 | 0 |

Source setting fixed from these footprints: `-j1 -M7000 -DElab.async=false`.
Every scope used `MemoryHigh=6500M`, `MemoryMax=7G`, `MemorySwapMax=0`,
`TasksMax=128`; all jobs were sequential. Before each final target the
existing populated, non-double-counted caps totaled 44.375 GiB; plus this
scope, 51.375 GiB, below the 55 GiB host limit. No other Lean process ran.
All final jobs had zero cgroup swap peak and zero OOM events.

The focused source checks were followed by one final four-file R0 replay,
including the integration/axiom audit; the unchanged Wide manifest was not
repeated. Final command, from the new build workspace, inside its own scope:

```sh
/usr/bin/time -v -o "evidence/Final-$name.time" \
  timeout --signal=TERM --kill-after=10 600 \
  /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env \
  /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -j1 -M7000 -DElab.async=false \
  -R /home/dombarker/project-offloads/aspis-r0-20261006/sources \
  -o "objects/R0/$name.olean" "sources/R0/$name.lean"
```

Final source records (paths relative to `lean/R0/`; PCQ means exactly
`[propext, Classical.choice, Quot.sound]` for every printed theorem):

| File | SHA-256 | Exit | Wall | Peak RSS KiB | Swaps | Axioms |
|---|---|---:|---:|---:|---:|---|
| Fold.lean | `fab2b0dc3cf0e32dd414e6737660d208989e2b8eb4ecd35eeb23354cd0e93329` | 0 | 3.92 s | 6809044 | 0 | 2 reports, PCQ |
| RoundNormalization.lean | `40b4abf0878b27e29d3f952c209bc2fb3d71ac0ced9efbf8d9185eabdd3511e4` | 0 | 4.41 s | 6767156 | 0 | 5 reports, PCQ |
| CitedKernelAudit.lean | `4c3ba9d5b698b955b639b40d01e80d298c4ef58d4a59a7d6332833cf883b22a5` | 0 | 1.17 s | 2354408 | 0 | 2 reports, PCQ |
| Audit.lean | `45038de83348884273bdc0d9222a4707a8c9c81898eb9b0e3fc73592939f81ed` | 0 | 2.84 s | 6732216 | 0 | 10 reports, PCQ |

The 19 reports include the new endpoints above and the existing wide initial
and final agreement, matched response, joint codeword list, and subfield
descent endpoints. Raw output, exact commands, resource/cgroup records, and
source hashes are retained in `evidence/Final-*.{stdout,time,json}` and
`evidence/final-manifest.json` on the build host. `Audit.lean` imports the Wide
results together with the new exact-encoder proofs; the literal V8 citation
audit is necessarily a separate Lean environment.

Failed attempts (all exit 1; no memory limit was raised):

- Combined Wide/R370 import: duplicate `AspisCircleTensorBinding.monomialToNatural` from V7 CircleNaturalBasis and V8 NaturalBasisCore; 1.68 s, 5667820 KiB, zero swaps; split the environments and prove the small exact-encoder formula directly.
- Fold-01: explicit unfolding of coordinate embeddings, restricted coordinate simplification, qualified `two_ne_zero`, and a theorem type annotation were needed; 3.33 s, 6784436 KiB, zero swaps; Fold-02 passed.
- RoundNormalization-01: nonexistent `Fin.val_three` and sparse-impulse simplification; 4.31 s, 6734088 KiB, zero swaps; use the literal small Fin value and symbolic child-index simplification.
- RoundNormalization-02: dependent decidable-`if` rewriting failed; 4.02 s, 6732388 KiB, zero swaps; simplify the explicit child index; RoundNormalization-03 passed.
- CitedKernelImport (R370 + WideTower): the same duplicate natural-basis constant; 1.79 s, 5655472 KiB, zero swaps; the R370-only import and audit passed.
- RoundNormalization-04: the new comparison witness needed an explicit coefficient-of-one simplification at index 4; 3.87 s, 6732484 KiB, zero swaps; RoundNormalization-05 passed.
- Local evidence-summary glob included a scope-command JSON list; restricted it to the four exact final target reports, then verified every local SHA against the compiled source.
