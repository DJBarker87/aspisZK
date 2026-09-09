# Fixed-width C1 gamma dots: a second measured saving

Research continuation of `b062f8ffa2efdc7c21312432530745df66bea5fa`,
2026-09-09. This consumes the fresh profile and the retained tag-offset kernel.

## Complete-transaction result

| Shape | Previous maximum | Fixed-gamma maximum observed |
|---|---:|---:|
| Transfer, current page | 1,096,831 | **1,083,060** |
| Transfer, rollover | 1,109,377 | **1,095,606** |
| Withdrawal, current page | 1,114,518 | **1,100,739** |
| Withdrawal, rollover | 1,127,798 | **1,114,035** |

Same-proof savings are **13,761–13,779 CU**, additional to the preceding
6,007-CU tag-offset saving. The worst observed complete transaction now has
**85,965 CU headroom** below the actual 1.2M TxV1 cap. All twelve maximum-body
successes use the identical archived **40,282-byte** proofs. Pool/Registry,
classic SPL Token3.5 SBF, account authentication, atomic settlement, heap request
and runtime configuration are unchanged.

All 24 maximum-body cases, 24 ordinary-body cases and two deliberate
post-real-verifier Token-CPI-failure rollback cases pass. Tested failure errors,
protected-account preservation and replay behaviour match the preceding build.
Successes use the pinned classic Token SBF; the intentional CPI-failure cases
retain the dedicated failing processor. These are fixture maxima, not universal
CU coverage. The same-pool selected V7 remains cheaper by **42,237 /61,205
/64,374 /65,151 CU**, so matched-V7 parity is not claimed.

[gamma-fixed-results.json](gamma-fixed-results.json) contains every CU/proof
identity, artifact hash, resource measurement and comparison. The driver uses
the real declared 1,200,000-CU limit, not its diagnostic override.

## Exact rewrite, including its formal boundary

The prior implementation loops over six four-product chunks, four M31 limbs,
and four fibre slots, followed by the final two C1 columns. The new
`fixed_dot::<L>` makes the chunk and limb indices compile-time constants and
uses a balanced seven-chunk sum. The outer four-slot loop remains. It keeps:

- The same 26 arbitrary canonical C1 coefficients per slot, in the same order.
- The same six four-product reductions and final two-product reduction.
- The existing partial-reduction policy and final canonical reduction.
- Every C2 helper product and all 152 packed-limb canonicality checks.

It does **not** assume that gamma^0 has a special representation, a helper is
zero, or any received residual is honest. Both input arrays are decoded in full
before arithmetic. The old loop remains available without `v8_gamma_fixed`.
No proof grammar, transcript message, check, round, mask or field is changed.

[GammaDotUnroll.lean](experiments/GammaDotUnroll.lean) proves:

1. The new balanced sum equals the old sequential sum for **any reducer**
   applied at the unchanged seven chunk boundaries.
2. If each reduced chunk is below 5p, the final sum is below 35p.
3. Every wrapping addition in the balanced word model equals its ordinary
   integer addition; therefore the new endpoint equals the old endpoint.

This reuses the unchanged four-product and partial-fold range facts from
`M31RangeKernels`/`QmCrossRange`, and their source audit. The new leaf is a
symbolic composition theorem, not a repeated proof of those old kernels. The
raw dot products, mask/shift reducer and decoder have not been modified.
The final bound includes the tail; no hidden incoming accumulator is assumed.

The source indices/chunk layout are inspected and differential-tested, not
translated into Lean. The claimed kernel proof is the seven-chunk integer/word
interface, **not** full Rust/LLVM/SBF acceptance equivalence. The deterministic
relation/image/row checks and their existing security scope are untouched.

The optimized actual-source test compares gamma reconstruction against
`gamma_combine_v6_packed_layer0` for **512 canonical profiles**, including all
152 single-coordinate bases, zero and maximal values. It separately tests
all-maximal C1 multiplier limbs, independent of a valid power sequence,
rejects p at each of the **152 packed positions**, and rejects two truncated
inputs. The fixed-width code passes all these checks. A new `--gamma-controls`
entry point avoids running unrelated prover/structured suites for this local gate.

## Evidence and resources

| Target | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| GammaDotUnroll focused Lean | 0 | 1.65 | 2,881,306,624 bytes | 0 |
| Optimized checked host build | 0 | 25.62 | 555,460 KiB | 0 |
| Named gamma controls | 0 | 0.01 | 2,464 KiB | 0 |
| Complete SBF build | 0 | 33.42 | 590,312 KiB | 0 |

Lean4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` reuse the
existing cache. Four final axiom audits list only `propext` and `Quot.sound`.
No `sorry` or new axiom is retained in a claimed result. Two small failed
preflights are archived separately: the runner initially omitted `-R` for its
external output file; then rewriting a composed function required an explicit
equality-transitivity application. Neither failure changed Rust or increased
resource limits. No unchanged formal suite was replayed.

NUC build scopes use High5/Max7 GiB/jobs2; controls and SVM use High3/Max4 GiB.
All use `MemorySwapMax=0`. Rust/SBF/LiteSVM versions and release settings match
the preceding [tag-offset report](tag-offset-review.md). Global overflow checks
remain enabled, apart from the individually bounded wrapping operations.

Selected ELF: **1,003,248 bytes**, **+3,984 bytes** over tag-offset.
SHA256 `2d16286eaa9f2dc76c2a4ab318bab3885d669be1253d82090cb48b3790c62ef1`.
The direct-r10 audit reports 4,096 bytes at entry/panic labels, with no new
stack warning. No extra heap is allocated. Query-source SHA256:
`bb497d35e1e5538480d48efc6d376984378d9dc756bb8288f0d5731103c228c0`.
The unchanged NUC field overlay has SHA256
`bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0`.

The body remains exactly
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes`.
Proving time/RSS/search were **not remeasured**. This run reuses public synthetic
proof fixtures; no recovered secret or proof binary is added to the repository.

## Reproduce and next decision

Run `run_gamma_fixed_lean.sh NEW_ABSOLUTE_LOG` for the changed leaf.
On the pinned task-owned NUC copy after all tag-offset overlays, synchronise the
research `query_arithmetic.rs`, `performance.rs` and changed runners, then:

```sh
bash experiments/run_complete_build_nuc.sh gamma-fixed-host NEW_HOST_BUILD.log
bash experiments/run_gamma_fixed_controls_nuc.sh NEW_CONTROLS.log
bash experiments/run_complete_build_nuc.sh gamma-fixed NEW_SBF_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh gamma-fixed NEW_MAX_DIRECTORY
ASPIS_V8_GAMMA_FIXED=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

Remove only `ASPIS_COMPLETE_MAX_FIXTURES` for the ordinary matrix.
`experiments/` abbreviates this research directory. Retain the driver's 1.4M
CLI runtime setting with its separate actual 1.2M transaction cap, as documented
previously. `audit_gamma_fixed.py` validates retained evidence without replays.

Retain the fixed-gamma version. The earlier profile already showed internal
authentication at about 146k CU; its shared two-tree walk and 53-byte parent
preimages are present, so neither is an unused saving. A concrete next control
is **byte-equivalent parent-preimage construction**: compare the current
contiguous 53-byte buffer against SHA input slices `[0x11], left26, right26`,
proving their concatenation equal and retaining every hash. The three-slice
syscall may cost more despite fewer copies; reject it on a measured regression.
This is an implementation control, not a new Merkle construction or a wider
digest claim. Full-transaction measurements, not hash-operation counts, decide.

The measured sub-1.2M result is now stronger, but not a production certificate
or a claim that all optimizations are exhausted. Matched-V7 parity, universal
CU, global recovery, adaptive full-view privacy and resource-bounded FS retain
their previous status. Security gets zero credit from work.
