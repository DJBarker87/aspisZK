# R41–R42: reviewed-pack arithmetic, unchanged research-v2 map

Base revision: `020ab456a0d50aad0b61317e06b2e024e897f677`, plus the
source-pinned R37 opening reuse and R38 grouped dot-product changes.
R38 primary diagnostic checkpoint: **20,229,550 CU**. This is not an
accepted transaction at the supported budget.

The supplied `aspis-r17-cu-review-20260921.zip` has SHA256
`fcf2e12be091e2d2e20bc3e0dc62490b4184dc377a5b191914328bdf2948a04b`.
All nine payload hashes match its manifest. Its seven quoted Git blob pins
match the cited `2c03cc7b` revision; its R36 review endpoint is our base
`020ab456`. We compose changes onto the retained R24-derived fixed FFT
endpoint `2b9ded2a3c8330239bdb0ad581785750eab71c54b069ad7764661d7058c02698`,
not the older fast-G template or the rejected DIF implementation.

## Mathematical boundary

For the same nodes 1 through 271 and arbitrary QM31 coins, cyclic G scales
coin a by `1-a^1024`, uses the existing numerator tree and a 1024-point FFT,
then divides by fixed nonsingular denominator values. Frequency zero is
filled from the original coins by `1024*c1 + sum(a>1) c_a*(1-a^1024)/(1-a)`.
The zero table entry is a sentinel, never a denominator inversion. This
is a fixed public exception, not an exceptional verifier challenge.

`lean/AspisV8R17/CyclicPowerSum.lean` proves six generic field lemmas:
the finite geometric value at a root, sum interchange, nonsingular spectrum,
the separate DC spectrum, the numerator/common-denominator identity, and
their combination. It does not yet prove the compiled Rust word algorithm,
the FFT/array correspondence, or the concrete constant inventory in Lean.
Finite basis tests do not silently discharge those source obligations.

Final focused compilation: `lake env lean -j1 -M2500` on that exact file,
cached `/Users/dominic/ZK/AspisFormal`, Lean 4.32.0. Exit 0, wall 8.59 s,
peak RSS 1,467,514,880 bytes, swaps 0. All six declarations report only
`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or new axiom.
Source SHA256: `d5eb4bde6ca2bc8c83f21a9051977d0469973917d5312c18bcd14f5659774048`.
Local development errors (a missing decidability instance and two symbolic
division/cancellation steps) were repaired in the leaf, without a manifest
replay or cap increase. [Final compilation](evidence/r17-cyclic-power-sum-lean-r42.log).

The carry change reorders only pure array reads into nested addition/halving.
It preserves the 513-entry chord intermediate and the grouped zero extension
at index 64. The pivot shortcut uses normal slot 15 times high slot 15,
halved eight times, in output slot 3. The retained R38 batched dot products
are not replaced by older generic contractions.

`NestedCarry.lean` proves the geometric-weight expansion of the recursive
nested expression and specializes it to one-half. It does not assert binary
index or Rust-word correspondence. Accepted evidence capture: cached
`lake env lean -j1 -M2500`, exit 0, 9.44 s, RSS 1,419,788,288 bytes, swaps 0;
both declarations use only `propext`, `Classical.choice`, `Quot.sound`.
Source SHA256 `48737258eb700cc9cd078ceeb916657137002a7e5b255b050e61c331689734c6`.
[Leaf compilation](evidence/r17-nested-carry-lean-r41.log).

## Independent supplied checker

The unchanged C++ `-O2` checker and Python generator pass: 542 CM31 basis
cases, 32 full QM31 vectors (64 componentwise three-way comparisons),
1023 nonsingular denominators plus the singular DC entry, two negative
controls, 82,000 carry cases, 80 grouped contractions and 80 pivots.
This is independent arithmetic evidence, not an Aspis Rust proof or CU test.

NUC scope: MemoryHigh 2G, MemoryMax 3G, MemorySwapMax 0, TasksMax 64.
Accepted run exit 0, wall 1.07 s, RSS 95,880 KiB, swaps 0.
[Checker log](evidence/r17-cyclic-pack-check-r40c.log),
[manifest](evidence/r17-cyclic-pack-manifest-r40.json).
The complete supplied pack is retained unchanged under
`tools/r17_cyclic_pack/`, including its independent checker and generator;
all manifest hashes were checked again after retention. Two earlier checker
runs lacked live in-scope cap evidence; their logs are retained separately.
The accepted record explicitly captures the live scope properties.

## Source/runtime boundary

Stages are generated in fresh workspaces by `stage_r17_carry_shortcuts.py`
and `stage_r17_cyclic_g.py`. Each verifies inherited source/core pins and
records exact before/after chains. Production protocol paths are untouched.
The old 2048 arithmetic, ordinary/dense comparisons, both complete verifier
paths, canonical checks, Merkle authentication and image constraints remain.

R41 carry/pivot-only SBF build passes source/table/frame gates: exit 0,
40.51 s, RSS 619,672 KiB, swaps 0 (5G/7G/zero-swap scope, TasksMax 128).
Same-proof primary checkpoint: **19,981,659 CU**, a saving of **247,891 CU**
against R38. G chord is 2,051,371 CU (down from 2,258,151), and ordinary
terminal is 1,277,725 CU (down from 1,318,836). Full honest diagnostic still
heap-aborts in the second reference pass at 23,176,531 CU; all four supported
1.2M/1.4M runs exhaust CU. No account changes or settlement. An initial
SVM launch had a mistyped executable path (exit 127, no ELF execution);
the corrected launch used the same accepted ELF without rebuilding.
[SBF log](evidence/r41/carry-build-r41.log),
[SVM observations](evidence/r41/carry-svm-r41.jsonl).

## Cyclic and combined measurements

The final cyclic Rust gate runs `r17-tensor-check`, which actually invokes
the staged fast-G controls. It passes all 271 input positions times all four
QM31 limbs, 32 complete three-way vectors (old 2048, cyclic 1024, independent
direct powers), dirty output buffers, all 271 scale/DC constants, all 1024
denominator identities and both malformed-algorithm negatives. The retained
FFT, hybrid-merge, field-boundary, full original-weight, dual/chord and fold
controls also pass. Both paths accept the identical v2 proof; the G-final
mutation rejects in the host gate. The profiler retains the same three G
tree/FFT markers, so none of the claimed arithmetic saving comes from
silently dropping those diagnostics.

| Stage | Primary CU | Saving against R38 |
| --- | ---: | ---: |
| R38 retained baseline | 20,229,550 | — |
| R41 nested halves + pivot | 19,981,659 | 247,891 |
| R42 cyclic full-output G only | 16,704,410 | 3,525,140 |
| R43 combined | **16,456,519** | **3,773,031** |

The final FFT interval is 3,040,361 CU, versus 6,613,168 before. The numerator
interval grows from 3,927,444 to 3,972,041 CU, including the new fixed scaling
and DC work. These are measured SBF intervals, not the pack's operation-count
prediction. All figures use the same fixture bytes and pinned VM driver.

The combined full diagnostic still heap-aborts in the second dense reference
pass, at 19,704,594 CU; cyclic-only does so at 20,091,292 CU. Neither is a
successful transaction. Mutated 100M diagnostic runs also heap-abort, without
the primary acceptance marker: do not call them completed checked rejections.
All 1.2M/1.4M cases exhaust CU; all accounts remain unchanged.

| Exact target | Exit | Wall (s) | Peak RSS (KiB) |
| --- | ---: | ---: | ---: |
| R42 tensor/cyclic host gate | 0 | 29.84 | 533,364 |
| R42 same-v2 proof audit | 0 | 39.55 | 534,332 |
| R42 G-final host rejection | 0 | 0.06 | 26,564 |
| R42 SBF build/frame gate | 0 | 56.19 | 619,864 |
| R42 SVM observation driver | 0 | 0.12 | 31,704 |
| R43 tensor/cyclic/carry host gate | 0 | 30.15 | 536,744 |
| R43 same-v2 proof audit | 0 | 11.85 | 454,188 |
| R43 G-final host rejection | 0 | 0.00 | 3,520 |
| R43 SBF build/frame gate | 0 | 41.53 | 619,124 |
| R43 SVM observation driver | 0 | 0.12 | 31,668 |

All report zero swaps. Host scopes: 4G/6G/zero-swap/Tasks128; SBF:
5G/7G/zero-swap/Tasks128; SVM: 3G/4G/zero-swap/Tasks64. Build times include
cache-lock waits where present; no cap was raised. Live SBF scope properties
were checked. Driver exit 0 is evidence collection, not verifier acceptance.

ELF SHA256:

- R41: `0f4ad29bd8cfeca7efa2f031985cc4b6fba23ea9e7becb477eeda87c5802f024`
- R42: `5e9ee14f5c79a0950657aa5093bc1602d2d61dc27ec535160a31084ca8015d56`
- R43: `9bfe8b9aa44717953045d6b38c934f2b1aa59fce4f8bb8161549f0dfd64bc942`

Proof SHA256: `d18b5455261d41ba2bbe8d44dd525faa057e50b5110f7cc4225ed32e298204f0`.
Driver SHA256: `34d87c8d4d5cb9b850e22342328ec9cc25e9f36435d982f47c69315ea9dbc2b4`.
[R42 Rust gate](evidence/r17-cyclic-g-r42c2-tensor.log),
[R42 CU observations](evidence/r42/cyclic-svm-r42.jsonl),
[R43 Rust gate](evidence/r43/cyclic-carry-host-r43.log),
[R43 proof/mutation](evidence/r43/cyclic-carry-proof-r43.log),
[R43 SBF build](evidence/r43/cyclic-carry-build-r43.log),
[R43 CU observations](evidence/r43/cyclic-carry-svm-r43.jsonl).

Reproduce by applying `stage_r17_carry_shortcuts.py` to R38 for R41;
`stage_r17_cyclic_g.py` to R38 for R42, or to R41 for R43. Then use the
pinned `check_r17_compact_control.py`, `check_r17_host_proof.py`, and
`build_r17_sbf_probe.py` runners in the above bounded cached NUC scopes.
An obsolete R42 draft/configuration failed before the accepted gate. Review
also caught incorrect draft test comparators/negative controls; these were
replaced before the final Rust run. Failed drafts are not arithmetic evidence.

## First remaining propositions

Formal arithmetic/source refinement: for every canonical 271-coin QM31 input,
the staged cyclic word routine returns exactly all 1024 source power sums,
with the same canonical encoding whenever its workspace allocation succeeds.
Connect the field spectrum lemmas, actual root/table inventory, FFT inverse
and array/word semantics; finite basis checks alone do not prove this bridge.

Diagnostic separation remains a separate gate: establish universally that
the retained combined-opening cross-check is redundant after the actual
two-channel domain/canonical/Merkle/relation checks. This batch deliberately
keeps that check and the second complete verifier. No failed check was deleted
to obtain the CU result. The next structural experiment is full compact-G
evaluation, recorded separately in `R17_COMPACT_G.md`.

These arithmetic changes do not establish full privacy or Fiat–Shamir
soundness for the research-v2 profile. R36's descriptor encoding/refinement,
joint commitments, shared-oracle chronology, semantic messages, openings,
failures, retries and publication obligations remain separate. No new hiding
assumption or protocol-format change is introduced by this batch.
