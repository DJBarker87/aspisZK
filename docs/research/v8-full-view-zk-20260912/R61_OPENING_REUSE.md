# R61: restore the retained fixed-width opening kernel

Base: `61b0a3ce324647396a9bf7e911222391e8126958` (R60).
Runtime control: selected R59, unchanged R19 proofs. Research-only branch
`research/v8-r61-opening-layout-20260929`; no production, protocol, wallet,
deployment or merge changes.

## Measured decision

| Complete primary verifier | R59 control | R61 | Saving |
|---|---:|---:|---:|
| World 0 | 1,516,838 | **1,507,423** | 9,415 |
| World 1 | 1,518,195 | **1,508,805** | 9,390 |

Both actual **1,000,000-CU-cap runs still exhaust**, as do their corrupt-final
controls at that cap. Under the diagnostic cap, both honest proofs accept and
both corrupt finals return a checked rejection, not a resource failure. This
is a recovered native optimization, not a sub-1M result. The slower fixture
still needs **508,805 CU** removed to reach 1M.

Same two distinct proof hashes, same driver, same 256 KiB heap and unchanged
accounts. The complete exact-text trace matches the clean world-0 CU. Its
1,402,360 executed instructions are 9,415 fewer than R59. The entire exclusive
function difference is `query_arithmetic::combine_beta`, 127,922 to 118,507.
All other exclusive function counts are unchanged. This is measured caller
attribution, not an estimate from multiplication counts.

Selected stage:
`/home/dombarker/project-offloads/aspis-r20-r61-opening-20260929-a`.
ELF SHA256:
`b000eb1c754c73b187b919161025c4bc3a449aa68ac99b3a1bad0286c50546c8`.

## What changed, and what did not

Source inspection found that R59 still contained `fixed_dot::<L>` but neither
its host nor SBF flags enabled `v8_gamma_fixed`. That kernel had already been
implemented, proved at the seven-chunk arithmetic interface, and measured in
the older optimized verifier. See the retained
[fixed-width review](../v8-no-work-100-20260907/gamma-fixed-review.md).
The cause of the historical flag omission is not established here.

R61 adds **only that flag** to the two staged build configurations. The only
Rust additions are host-only controls and their host entry point. The runtime
source text is otherwise byte-identical to R59. The stage manifest now also
explicitly pins both build-configuration files (197 pins versus 195).

For each of four limbs and four opening slots, the enabled kernel specializes
the same six four-product chunks and final pair, then balances the same seven
partial sums. It retains the same mixed-width arithmetic, coefficient order,
partial-fold boundaries, final canonical reductions and three helper products.
The R55 caller-buffer decoder still checks all 152 limbs, including coefficients
whose contribution vanishes at beta zero or one. Error ordering is unchanged.
No transcript, commitment, seed, challenge, point, query, image constraint or
final relation was removed or changed.

The initially considered coefficient-layout experiment was not implemented:
the retained fixed-width kernel was tested first. The old four-channel fusion
was already measured slower; it was neither rerun nor selected. This follows
the instruction to reuse the optimized baseline rather than rediscover it.

## Checked boundary

Fresh optimized actual-source checks passed:

- 16,384 scalar comparisons against independent u128 dot sums, covering
  4,096 arbitrary canonical coefficient matrices, maximal limbs and all basis
  positions; these need not be valid gamma-power tables.
- 4,096 packed-record comparisons using those arbitrary matrices.
- Retained 2,048 beta-combination comparisons, 2,232 malformed/error-order
  checks and poisoned-output controls; beta zero and one included.
- Retained 512 canonical gamma profiles, maximal coefficients, all 152
  noncanonical positions and two truncations against the independent source.
- 3,281 complete host wire cases: one acceptance and 3,280 checked rejections.
- Both unchanged full host proofs, SBF build without stack-frame warnings,
  and the complete SVM runs described above.

**No new Lean theorem or compilation is claimed.** The unchanged
`GammaDotUnroll.lean` source hash matches its retained successful compilation
log. Its four audited theorems establish balanced-versus-sequential summation,
range and wrapping equality for the same seven chunks. Only standard
`propext`/`Quot.sound` appear. The unchanged `M31RangeKernels` and `QmCrossRange`
facts supply the four-product and partial-fold arithmetic bounds. Source
indices and actual kernel behavior are checked, not universally extracted
into Lean. No unchanged formal suite was rerun.

The Solana development skill kept selection at the malformed-input, stack
and complete-execution boundary, rather than a host timing or operation count.

## Resources and reproduction

All new jobs ran on the NUC via Tailscale, release/offline/locked/jobs=2.
Builds used MemoryHigh=5G/MemoryMax=7G; runtime/trace used 2G/3G; staging and
collection used 1G/2G. All scopes used MemorySwapMax=0 and TasksMax=128, with
at most 7 GiB simultaneous reservation. Every timed command exited 0 with
zero swaps.

| Target | Wall seconds | Peak RSS KiB |
|---|---:|---:|
| Focused source-check compilation | 20.16 | 517,708 |
| Focused source checks | 0.04 | 1,936 |
| Complete host compilation | 9.18 | 356,256 |
| Wire controls | 5.46 | 19,936 |
| SBF runner, including basis check | 35.11 | 600,296 |
| SVM world 0 / world 1 | 0.05 / 0.05 | 21,944 / 22,400 |
| Exact-text full trace | 0.83 | 157,620 |

Use `tools/stage_r61_opening.py` with the pinned R59 stage, followed by
`tools/run_r61_full.py --mode host`, `--mode sbf`, then `--mode svm` in the
bounded scopes above. The stager refuses mismatched parent hashes. Preserve
the exact unstripped ELF before another SBF build if tracing. No fixture or
key regeneration is needed.

Local evidence-only audit:

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r61_evidence.py
```

The collector excludes keys, proof binaries and raw trace registers. The
committed evidence contains source/configuration deltas, resources, public
execution receipts and exact-text instruction summaries.

## Remaining work

Next CU target: repeated general products in the ordinary-terminal correction
and semantic callers, using retained call-PC evidence. General QM31 multiply
still accounts for 310,483 exclusive instructions across 2,171 calls. That
count is not a prediction of removable cost. Restore other old optimizations
only after checking applicability to the repaired source; do not enable old
protocol-specific assumptions wholesale.

First remaining security proposition is unchanged from R60: actual generated
square-loop and guarded inverse execution must refine the proved canonical
word chain, followed by word-level norm/equality/try-inverse composition.
Full shared-oracle, seed/commitment, prover/observer, semantic/opening,
failure/retry/publication composition and justified loss bounds remain open.
Coherent pre-beta quotient-pair extraction remains a separate soundness
obligation. C1's negative regression, fixed-block hiding, local joint coverage
and full-transcript privacy remain distinct. This CU saving closes none of
those cryptographic obligations.
