# R39–R40: prefix plus complete geometric G functional

This separate candidate predates integration of the reviewed cyclic-G pack.
Base: `020ab456` plus R37/R38. Preserve it as a different algorithm, not as
the pack's full-output cyclic transform.

The R39 FFT produces only the first 479 coefficients. Its numerator degree
270 and inverse-series-prefix degree 478 sum to 748, below 1024, so these
low coefficients do not alias. The other output entries are scratch, not
an asserted full G vector. The pivot is separately computed from all 271
coins and the retained 1023rd power row.

`GPrefixConvolution.lean` proves the symbolic no-wrap, convolution rewrite
and inverse-prefix truncation lemmas. Exact worktree leaf, cached Lean 4.32.0,
`lake env lean -j1 -M2500`: exit 0, 55.13 s, RSS 1,383,596,032 bytes,
swaps 0. Axioms: `propext`, `Quot.sound`, and `Classical.choice` for the two
finite-sum results. No source FFT or global security claim.

Optimized Rust table generation: exit 0, 26.37 s, RSS 537,424 KiB, swaps 0.
Table SHA256 `92c5976bcd024fdea47a1faacbf0488915001bd2071294654eaf157e21c1af4a`.
Prefix control: six unequal-lane vectors and all 271 basis positions match
the full source on entries 0..478; exact pivot and root/no-alias controls
pass. Exit 0, 0.99 s, RSS 277,772 KiB, swaps 0.

R40 retains the full functional: all 271 geometric rows over all 1024
coordinates, both base tensor contributions, sparse permutation correction,
inactive/pivot correction and the same image residual. No used mask is
resampled. Only public fixed node powers are M31; coins and challenges
remain QM31. Selected claim entries and the terminal use the actual source
map. The four real folding challenges are retained.

Host controls: 2,184 specialized geometric comparisons plus 32 direct source
chord/fold comparisons, exit 0, 28.34 s, RSS 535,928 KiB, swaps 0.
Complete G control: 16 terminal and 32 selected-pair comparisons against
source original/dual/chord/four-fold; zero terminal allocation attempts.
Exit 0, 29.77 s, RSS 536,324 KiB, swaps 0.
Same research-v2 fixture accepts in both full host paths: exit 0, 13.24 s,
RSS 459,300 KiB. G-final mutation rejects: exit 0, 0.00 s, RSS 3,520 KiB.
Both report zero swaps. All heavy gates used 4G/6G/zero-swap scopes,
TasksMax 128, optimized Rust and the retained host cache.

The generic rejection marker says `R17_LEGACY_PROFILE_REJECTED`; in this
runner it tests the G-final byte mutation, not a second old-profile fixture.

Evidence: `evidence/r17-g-prefix-*-r39.*`,
`evidence/r17-g-geometric-*-r37.*`,
[R40 source controls](evidence/r17-compact-g-host-r40.log),
[same-proof and mutation](evidence/r17-compact-g-proof-r40.log).
The first prefix staging attempt rejected an obsolete fast-G template pin;
the replacement verified the actual R24 fixed-FFT hash chain. No pin waiver.

## R44 actual SBF result: do not promote over R43

After the reviewed-pack arithmetic measurements, the same compact-G candidate
was composed with the R41 pure-read carry/pivot shortcuts and measured on the
unchanged v2 fixture. Source/table/frame gates pass. The primary accepts at
**18,281,174 CU**, which is **1,824,655 CU slower** than R43's cyclic+carry
16,456,519. R43 remains the best measured candidate.

Compact-G preparation costs 8,482,409 CU; its complete geometric terminal
costs 5,503,873 CU. Ordinary terminal costs 1,277,747 CU. Removing expanded
G dual/chord vectors did not by itself make this full functional inexpensive.
The entire diagnostic still heap-fails in the second reference pass at
24,907,558 CU. All supported 1.2M/1.4M cases fail the CU meter. No account
changes, wallet operation, deployment, or checked SVM rejection is claimed.

| R44 exact target | Exit | Wall (s) | Peak RSS (KiB) |
| --- | ---: | ---: | ---: |
| Complete G/claim/allocation source control | 0 | 29.67 | 536,528 |
| Same-proof host audit, both paths | 0 | 13.09 | 459,976 |
| G-final host mutation rejection | 0 | 0.00 | 3,696 |
| SBF source/table/frame build | 0 | 43.91 | 619,072 |
| SVM observation driver | 0 | 0.14 | 37,628 |

All report zero swaps. Host 4G/6G/0 swap/Tasks128, SBF 5G/7G/0/Tasks128,
SVM 3G/4G/0/Tasks64. Live SBF properties were inspected. An initial host
runner path error exited 2 before compilation; the corrected root-level
runner used the same staged source without a cap increase.

ELF SHA256: `bb0c9f432510331fc2358c9a0ded6b04174ce1012b7077624274fceb54c901ad`.
Proof SHA256: `d18b5455261d41ba2bbe8d44dd525faa057e50b5110f7cc4225ed32e298204f0`.
[Source gate](evidence/r44/compact-g-carry-host-r44.log),
[proof/mutation](evidence/r44/compact-g-carry-proof-r44.log),
[SBF build](evidence/r44/compact-g-carry-build-r44.log),
[SVM observations](evidence/r44/compact-g-carry-svm-r44.jsonl).

Reproduce R44 by applying `stage_r17_carry_shortcuts.py` to the retained R40
stage, then the focused control, proof, build and SVM runners. R44 is not a
composition with the cyclic full-output transform: its first-479 prefix and
separately retained full geometric tail are a different exact-map algorithm.

First remaining source proposition: the compiled prefix, geometric kernel,
selected entries and sparse corrections equal the full transported source
functional for every canonical input, including its invalid-proof image
terms. Generic algebra and finite actual-source controls do not alone prove
that refinement, full privacy, or soundness preservation.
