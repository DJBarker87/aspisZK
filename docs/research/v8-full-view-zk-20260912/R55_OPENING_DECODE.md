# R55: packed opening decoder, exact canonicality marker

Base: `85f18af7ce9078b751ca1b8fb981f1ce35396499` (R54).
Branch: `research/v8-r55-opening-decode-20260929`.
Execution control: selected R27 shared-block stage, manifest
`3c0741beddf4bc794a0e21fccc38fcfda7fd9aa227b0b2a3104d8121bd147f79`.

## Measured result

| Complete primary verifier | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| R27 control | 1,620,236 | 1,621,719 | Retained control |
| Caller-owned decode buffers only | 1,621,490 | 1,622,965 | Reject standalone |
| Buffers plus high-bit canonicality marker | 1,612,162 | 1,613,637 | Select |

The selected change saves 8,074 / 8,082 CU (about 0.5%). These are complete
diagnostic-cap runs, not a supported-budget result. Both honest proofs and
both corrupted-final controls exhaust at the actual 1,000,000-CU cap.
At the diagnostic cap both honest proofs accept and both corrupted finals
return checked Custom(6) rejections, not resource failures. The two distinct
proof hashes, runner, 256 KiB heap and account-state checks match the control.
No second verifier is counted or removed in this milestone.

## Source delta and proof

The staged `query_arithmetic::combine_beta` retains the original arithmetic
after decoding. C1's 104 limbs and C2's 48 limbs are decoded into caller-owned
buffers. The original decoder is retained for host-only differential testing.
Bytes, bit layout, C1-before-C2 error order, coefficient preparation and all
authenticated inputs are unchanged. Zero beta/one beta do not bypass any limb
validation. There is no `unsafe` code, unchecked uninitialized buffer or
global overflow-check change.

For each already-masked 31-bit limb `v`, the selected decoder accumulates
`invalid |= v + 1` and rejects if `invalid >> 31 != 0`. Because `v <= P`,
where `P = 2^31 - 1`, the addition fits in u32 and its high bit is set exactly
when `v = P`. OR preserves the existence of such a limb. This replaces the
old OR of boolean equality flags, not the canonicality predicate itself.

`AspisV8R19/PackedCanonicalMarker.lean` proves five statements: addition
bounds, the one-word marker, shift/OR accumulation, zero flags iff no P,
and equivalence with every limb being strictly below P. All five axioms
audits report only `propext` and `Quot.sound`. The focused leaf compiled in
1.50 s, peak RSS 3,258,748 KiB, zero swaps, exit 0. The first failed local
proof attempt (an unavailable lemma name) is retained. The reused final
cache has 287 successful objects; no package-wide replay was run.

This proves an integer predicate, not universal Rust/compiler extraction.
The sequential imperative OR and the list OR express the same associative,
commutative accumulation; no full machine-code refinement is claimed.

## Executed checks and attribution

Each candidate passed:

- 2,048 actual-source combination comparisons against the original routine;
- 1,024 poisoned-output buffer checks;
- 2,232 malformed-length, noncanonical-limb and error-order controls,
  including all 152 limb positions at beta zero, one and minus one;
- the retained 3,281-case full-wire gate (3,280 checked rejections);
- both unchanged honest proofs on the host;
- SBF build/stack gate and complete SVM checks described above.

The selected ELF is
`d12bca4821db52cb854b9255c4938459e524e3ed7008d87be91b541ee0dfdc54`.
An additional full world-0 instruction trace has identical clean CU and
byte-identical deployed/unstripped `.text`. It executes 1,507,099 instructions,
6,534 fewer than R27. General QM31 multiplication remains 327,881 exclusive
instructions across 2,171 entries: this decoder does not improve that kernel.
The decoder is now partly out-of-line, so comparing `combine_beta` alone
would overstate the saving; the complete execution is the acceptance metric.

## Reproduction and resources

`stage_r55_opening.py` verifies the exact R27 manifest and all 182 parent pins,
then creates a fresh isolated stage with 183 pins. Only the query-arithmetic
source, host Cargo test entry and added focused test file differ. No production
protocol paths in the repository were edited. Use `--branchless` for the
selected stage; omit it to reproduce the rejected buffer-only experiment.

On the pinned Linux build host, with the existing cached tools/workspaces:

```sh
python3 stage_r55_opening.py --control /home/dombarker/project-offloads/aspis-r20-shared-blocks-20260928-a --output /path/to/fresh-stage --branchless
python3 run_r55_full.py --stage /path/to/fresh-stage --mode host
python3 run_r55_full.py --stage /path/to/fresh-stage --mode sbf
python3 run_r55_full.py --stage /path/to/fresh-stage --mode svm
```

These are inner commands, not permission to run uncapped builds. Each was
wrapped in its own systemd user scope with MemorySwapMax=0 and TasksMax=128.
Host/SBF builds used MemoryHigh=5G/MemoryMax=7G; SVM/trace 2G/3G; Lean 3G/5G;
staging/collection/analysis 1G/2G. Maximum simultaneous reservation was 12 GiB
when Lean overlapped compilation. Cargo used release, locked, offline,
two jobs and enabled overflow checks. Compilation was the expensive phase;
there was no debug arithmetic gate. Raw traces, binaries and build keys remain
on the host, outside the committed compact evidence.

Local evidence verification (no heavy replay):

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r55_evidence.py
```

The gate checks exact generated source, retained errors, proof/runner hashes,
all new logs, the five axioms audits, 287 cached source hashes and the full
execution trace receipt. It deliberately reports `actual_1M_gate_passed=false`
and `full_privacy=false`.

## First remaining obligations

Performance: remove another 613,637 CU from the slower fixture. Next inspect
the actual general QM31 multiply/short-dot instruction costs and semantic
selector reuse. Do not repeat rejected R24 inlining or R26 schoolbook layouts
without a specific new source or compiler reason. Keep only full-run winners.

Privacy: R54's universal Rust sampler/field correspondence, especially the
guarded circle inversion, remains unproved. Complete prover/observer chronology,
shared-oracle first reads/prequeries, seed/commitment hops, all cuts, retries
and publication still need composition and justified loss bounds. R50's
degree-819 fixed-root polynomial is not an independent-uniform source law.
Pre-beta coherent extraction remains a separate soundness obligation.

No negative regression was removed, no new hiding assumption introduced,
and no global privacy/soundness theorem is claimed. No merge, deployment,
settlement or wallet operation was performed.
