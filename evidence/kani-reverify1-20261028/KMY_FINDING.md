# KMY window re-verification

Frozen revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.

Stage 1: original assertions and copy lengths under inspection. No credit restored yet.

Budget: Kani 0/60, Lean 0/60, Rust 0/5. Host scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one at a time. Existing launchers only. No release source changes.

## Stage 2: expand_values

LPn_K001: window PASS KMY_K006 (explicit validated loop, 16 bytes, arbitrary offset 0..80 in 96 arbitrary bytes); zero window PASS KMY_K007; original slice pointer/length premises PASS KMY_K008. L002 compiles `LPn_step_frame`, exactly the original byte assertion. Source correspondence: the frozen body has one 16-byte copy followed by one 16-byte fill for its sole admitted chunk. `KMY_expand_values.frozen.rs.txt` retains that body. No Rust-to-Lean compiler refinement is claimed.

K001 unsupported own option; K003 missing own PATH entry; neither reached verification. K004 passed but optimized trace did not reach the replacement: excluded from mitigation credit. K006 explicitly calls the identical validated loop. L001 failed draft; L002 has only propext, Classical.choice, Quot.sound.

## Stage 3: wide_view

LPa_K015 remains OPEN. KMY_K009 explicitly reaches the validated loop but the arbitrary 32-byte window over all 57,607 backing bytes times out at 90 seconds (6,473,584 KiB peak RSS). KMY_K010 splits after the copy, retaining the frozen wide_view body and original pointer/layout assertions; it also times out at 90 seconds. No counterexample was produced. Neither is rerun unchanged. Remaining split: prove the 32-byte region and exterior frame separately, then split parse rejection/value acceptance from view slice layout.

## Stage 4: six-wide serializer windows

KMY_K011 PASS: actual frozen WideExact serializer, canonical arbitrary eight limbs, all 32 encoded bytes, then a validated 32-byte copy into arbitrary pre-state at arbitrary offset in a 64-byte parent. Every exterior byte is framed. KMY_K012 PASS: arbitrary four-byte limb window and shift/byte projection. KMY_L003 compiles `wide_six`: six 32-byte windows give exactly `raw[j/32][(j%32)/4][j%4]` for every j<192. It also compiles append length/value and joined-digest composition. All axioms accepted.

The source overlays are generated from the frozen revision by KMY_prepare_serializers.py; only the module path and explicit validated copy calls change. Original and overlay SHA-256 values are in KMY_serializer_sources.json. These remain value-level composition results; allocation/growth integration is still a separate obligation for the Vec harnesses.

## Stage 5: checkpoint value compositions

KMY_L006 compiles the exact local byte formulas for append32, query-word append, selected reference at 712+16*i, put_k/put_e at arbitrary prefixes, checksum projection, digest prefix, roots/queries and semantic/z. KMY_L005 proves translation of local windows to arbitrary global origins; the global frame law is unbounded in KMY_L002. Each theorem has accepted axioms only. KMY_L004 was a failed draft (reserved identifier and unavailable Mathlib tactic), corrected without changing statements.

KMY_K013/K014: full 1768-byte parent windows16/32 TIMEOUT; KMY_K015: window4 PASS. KMY_K016 failed only the destination initializer's unwind assertion (66 elements with bound65), leaving all value checks undetermined. A corrected actual-QM31 window is KMY_K028. This is a setup-bound failure, not an original-property counterexample. KMY_K017 actual arbitrary-bit QM31 serializer window16 PASS. KMY_K018 local arbitrary-source window32 PASS.

The first three full-array invalid-limb view cases also timed out (K020–K022); K023–K027 were deferred before admission after identifying the shared full-array graph. Replacement splits are local parse acceptance and constant-data pointer metadata (K030/K031).

## Stage 6: concrete six-wide append closure

KMY_K040–KMY_K045 all PASS. These are six distinct constant-position heap steps, with arbitrary pre-existing prefix bytes and an arbitrary canonical eight-limb value, at (length,capacity)=(0,0),(32,32),(64,64),(96,128),(128,128),(160,256). Each checks output length, every prefix byte and every appended serializer byte. This replaces KMY_K029's timed-out symbolic stage; no unchanged rerun. KMY_L003's wide_six and KMY_L007's six_lengths compose those steps into exactly the original 192-byte assertion for LPb_K016 and LPe_K005. Their earlier selected-property credit is restored under the validated-stub scope.

KMY_L007 also compiles to_vec value identity, generic retained-prefix growth and the original prefix bounds. KMY_K034–KMY_K037 confirm the source-cut oracle chronology/metadata, including physical 57607/1880 inputs; they do not by themselves close the large initial-body/growth bridge. KMY_K038 proves the local arbitrary-bad-limb rejection. KMY_K032 and KMY_K033 timed out after splitting the typed copy and iterator continuation; typed-weight credit remains open.

## Stage 7: wide_view decoder boundary closure

KMY_K072 PASS for all 32-byte inputs: actual frozen decoder acceptance iff all eight decoded u32 limbs are canonical, with every accepted limb equal to its byte decoding. KMY_K073 PASS: the frozen wide_view body with only its decoder call parameterized accepts an arbitrary canonical Some(E) or None; it checks the decoder input's exact pointer/length and every original success/error and slice-layout assertion. KMY_L008 proves that reading the global copied window gives the original 32 source bytes, hence every pure decoder receives exactly the same input. Together with K018 and L005, this replaces the timed-out full-array attempts and restores LPa_K015.

K065/K066/K070/K071 were compile-only failures in our constant extraction (missing FIXED); the frozen FIXED declaration was added for the corrected runs. These are retained and counted. K064/K067–K069 are deferred before admission to preserve the run budget for the corrections and fourteen semantic/z stages. No original counterexample was produced.
