# R56: delay two intermediate product reductions

Base: `ad3e1634e711f1c1aeaf97271c4934eb07697b5c` (pushed R55).
Branch: `research/v8-r56-partial-product-20260929`.
Control: the selected, source-pinned R55 decoder stage. Protocol, proof bytes,
sparse G, T163, all transcript rules and all validation checks are unchanged.

## Exact result

| Complete primary verifier | World 0 CU | World 1 CU |
|---|---:|---:|
| R55 control | 1,612,162 | 1,613,637 |
| R56 partial product | **1,586,096** | **1,587,563** |
| Saving | 26,066 | 26,074 |

Select R56. The improvement is about 1.6%, not a solution to the CU target.
Both honest fixtures still exhaust at the actual 1M cap; another 587,563 CU
must be removed from the slower fixture. Diagnostic runs complete and accept
both distinct unchanged proofs. Corrupted combined finals return checked
Custom(6) errors under the diagnostic cap and resource failures at 1M.
Heap remains 256 KiB; simulated accounts remain unchanged. No deployment,
transaction submission, settlement, wallet operation or merge occurred.

## Arithmetic change

The already-selected guarded schoolbook multiplier computes two intermediates
`u = c*g - d*h` and `v = c*h + d*g` modulo P. R55 fully canonicalizes these
before reconstructing and canonicalizing the four output limbs.

R56 uses one Mersenne fold for those intermediates:

```
foldOnce(x) = (x & P) + (x >> 31),  P = 2^31 - 1.
```

For these two inputs, `0 <= x < 2P²`, so the folded representative is below
3P and has the same residue. The first output's subtraction offset must
therefore increase from P to **3P**. This is essential: the old canonical
intermediate bound is no longer valid. The offset still vanishes modulo P.
Every staged addition and subtraction remains a nonnegative integer below
2^64. All four final outputs use the original full-range canonical reducer.

The eight-limb canonical guard is byte-for-byte unchanged, as are the general
noncanonical fallback and prepared-multiplier construction. The general
reducer is not weakened. No public canonicality premise is newly assumed.
Only the research stage's `r24_guarded_qm.rs` executable helper changes;
other changed files are a host test, its Cargo entry and frozen source copies.
The repository's production protocol paths are untouched.

## Formal and actual-source gates

`AspisV8R19/PartialProduct.lean` compiles nine theorems covering:

- residue preservation and the below-3P bound for one fold;
- canonical-product and intermediate integer bounds;
- the new reconstruction's addition/subtraction bounds;
- vanishing offsets and the literal bit-mask/shift form;
- equality of the reconstructed first two coordinates in `ZMod P`.

The first six statements compiled in 1.87 s. Adding the source bitwise and
reconstruction bridge gave the final **exit 0, wall 2.07 s, peak RSS
3,239,996 KiB, zero swaps**. All nine axioms audits use only `propext`,
`Classical.choice`, `Quot.sound` (one theorem is axiom-free). Cached workspace:
Lean 4.32.0, 288 successful source-pinned objects. No package-wide replay,
cold dependency build, `sorry`, large numeral normalization or new axiom.
These are arithmetic/source-shaped leaves, not universal Rust/SBF extraction.

Actual optimized Rust checks:

- 265,536 operand pairs: all 65,536 combinations from four boundary limb
  values across eight positions, plus 200,000 deterministic random pairs;
- multiplication against both the frozen R55 field and an independent u128
  formula; prepared multiplication and one-term checked dot on every pair;
- 24 invalid raw-constructor cases retaining the old public fallback result
  or panic, and checked-dot rejection;
- retained 600,192 small-dot comparisons, 576 complete dot vectors through
  length 4,096, 7,272 noncanonical cases and two length errors;
- 3,281 full-wire controls, including 3,280 checked rejections, both honest
  host fixtures, stack-safe SBF compilation and complete SVM executions.

Finite comparisons are not claimed as a universal arithmetic or privacy proof.

## Attributable complete-execution saving

The additional world-0 instruction trace reproduces clean **1,586,096 CU**.
Deployed and unstripped `.text` are checked byte-identical. It executes
1,481,033 instructions, 26,066 fewer than R55. After removing only Rust hash
suffixes from symbol names, the exclusive function differences are exactly:

| Function | Fewer executed instructions |
|---|---:|
| General QM31 multiplication | 17,398 |
| Checked dot | 6,176 |
| Prepared QM31 multiplication | 2,492 |
| Total | **26,066** |

All function entry counts and all other exclusive function totals are
unchanged. The whole trace has the same 75,445 integer-multiply instructions;
the saving comes from the changed reduction work and its compiled lowering,
not fewer field products. This does not imply constant savings on every input.

Selected manifest:
`c2f16a9063dbf24580b1537fef0bffac4c3081276fe41774be01f83c28b4e5e9`.
Selected ELF:
`13c57487a90d0bd4df38e477fd35bb7840d665aa4cab15c0683de02106e74a4e`.
NUC stage: `/home/dombarker/project-offloads/aspis-r20-r56-partial-product-20260929-a`.

## Reproduction and evidence

Stage with `stage_r56_product.py --control R55_STAGE --output FRESH_STAGE`.
It checks the exact R55 manifest and all 183 parent pins, adds the frozen
reference/test sources, then records 188 pins. Run `run_r56_full.py --stage
FRESH_STAGE --mode host`, then `sbf`, then `svm`. The retained output directory
names `r24-*` are runner conventions, not older source versions.

All heavy work ran on the NUC via Tailscale in separate systemd scopes:
Rust builds 5G/7G high/max; Lean 3G/5G; SVM/trace 2G/3G; staging and analysis
1G/2G; MemorySwapMax=0 and TasksMax=128 throughout. Maximum overlapping
reservation was 12 GiB. Compilation was the expensive phase. Release,
offline, locked, two-job Rust builds retained overflow checks and cached
dependencies. The Solana development skill's source/stack/complete-runtime
checks determined selection; operation counts alone did not.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r56_evidence.py
```

The compact evidence includes source deltas, frozen references, manifests,
commands, logs, exact timings/RSS/swap, axioms audits, CU and trace receipts.
Raw trace registers, binaries and build keys remain on the NUC and are neither
exported nor deleted. Existing scratch work and negative regressions remain.

## Remaining boundary

Performance: inspect semantic selector/common-factor reuse and the remaining
native caller work. Do not infer the 1M goal follows from these savings.

Privacy: universal Rust sampler/field correspondence, especially guarded circle
inversion, remains the first source-refinement obligation. Full chronology,
joint masking/posterior coverage, semantic cuts, simulator/commitment/seed
hops, actual shared-oracle challenge law, retries and publication still need
composition with justified loss bounds. R50's degree-819 conditional polynomial
bound is not a source-distribution bound. Coherent pre-beta quotient extraction
remains a separate soundness task. **No full privacy or soundness claim.**
