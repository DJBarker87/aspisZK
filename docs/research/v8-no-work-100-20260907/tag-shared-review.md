# Shared tag sums: eliminate repeated accumulation across kernels

Research continuation of `50186b8ba739e0f0a0fb141ef19265c91b9e605a`,
2026-09-09. This consumes the previous bounded tag-prefix and shared-selector
results. It does not change production source, main, transcript or proof grammar.

## Measured outcome

| Complete transaction | Previous bounded-tag maximum | Shared-tag maximum observed |
|---|---:|---:|
| Transfer, current page | 1,106,879 | **1,102,838** |
| Transfer, rollover | 1,119,414 | **1,115,384** |
| Withdrawal, current page | 1,124,560 | **1,120,525** |
| Withdrawal, rollover | 1,137,838 | **1,133,805** |

Every row covers three predetermined archived **40,282-byte** proofs, executing
the same complete account authentication, Registry and atomic Pool settlement
with the explicitly pinned classic SPL Token 3.5 SBF. All run under the real
1,200,000-CU TxV1 cap without the diagnostic runtime override. Same-proof savings
are **4,030–4,044 CU**, with **66,195 CU** worst-observed headroom.

The new selected build also passes 24 ordinary-body cases and two deliberate
post-real-verifier Token-CPI-failure rollback cases. The maximum-body matrix has
24 cases, including altered-proof, wrong-release, stale-lane and replay controls.
All tested failure outcomes agree with the preceding build, and protected
accounts remain unchanged. The CPI-failure controls retain the dedicated
failure processor; successes use the classic Token binary. The driver's
unsupported rollover stale/replay cases are not counted.

These are fixture maxima, not universal CU bounds. The same-pool selected V7
control remains cheaper by 62,015 / 80,983 / 84,160 / 84,921 CU respectively.
Its original release build policy is retained; V8 retains global overflow
checks and the previously proved bounded kernels. See
[tag-shared-results.json](tag-shared-results.json) for every proof hash,
individual CU result, unchanged errors and evidence links.

## The exact shared computation

The prior tag-prefix kernel computes, per coordinate and M31 limb,
`S=sum(a_i)` and `D=sum(i*a_i)`, and reduces `67*rotated(S)+D` once. The copy
selector stage already computes most of the corresponding **field-valued**
selector sums. Rebuilding S in the tag loop is redundant, provided the
reduced-sum interface is established rather than assuming raw equality.

[generate_tag_shared.py](experiments/generate_tag_shared.py) consumes the pinned
old scatter generator and its unchanged outputs. It finds **24 of 30 sums**
as an existing input or one of the existing 59 addition nodes. The other six
require **14 additional QM31 additions**. The new selected entry point computes
the original 59 nodes once, fills the original 73 selector/pattern cells exactly
as before, then stores thirty tag sums in previously unused scratch cells.

There is no second call rebuilding the old plan, no additional vector allocation
and no prover-supplied sum. The old generated Rust and all its Lean outputs are
byte-identical; a separate generated entry point enables the comparison and
keeps earlier evidence reproducible. All pattern contributions remain present
even when their corresponding public copy weight is zero.

The tag kernel reads the stored canonical QM31 sum and accumulates only D. This
removes **1,088 raw u64 S additions** across the 272 endpoints, while charging
the fourteen new field additions, stores and changed calls. The same thirty
tag coordinates still use **120 limb reductions**. That operation count is not
the CU claim; the complete SBF comparison above establishes the saving.

## Formal interfaces and actual-source tests

| Result | Exact scope |
|---|---|
| [CopyTagSums.lean](experiments/CopyTagSums.lean), `all_tag_sums` | All thirty generated sums equal the literal frozen endpoint sums, for arbitrary selectors over any commutative ring |
| [CopyTagShared.lean](experiments/CopyTagShared.lean), `reduced_sum_mod` | Replacing S by `S mod p` in the tagged accumulator preserves its residue |
| `shared_accumulator_mod` / `shared_loop_endpoint` | Literal tagged dot product equals the reduced-S implementation modulo p, and its final raw accumulator fits u64 under the actual canonical/offset/count bounds |
| Existing `CopyTagSplit` prefix/product theorems | The remaining D products and all prefix sums are bounded; the selected wrapping operations equal ordinary arithmetic |

The key distinction is that the stored S is not the old unreduced integer.
The new modular bridge proves precisely why this is permissible. No inverse,
nonzero selector, honest-zero residual or successful-payment premise is used.

The thirty ring identities reuse the checked `CopyScatterNodes` specifications.
Their final aggregation uses two fifteen-cell tables, retaining the earlier
sparse/shallow proof-generation discipline. The generator independently checks
every sum as an integer coefficient vector against the actual source table.
It fails closed if its frozen generator, table or outputs change.

[copy-tag-shared.patch](experiments/copy-tag-shared.patch) selects the new
function only under `v8_copy_tag_shared`, requiring the existing scatter and
bounded-tag configuration. It compares the old and new 73-cell suffix, each
stored S, and each final tag value against both the literal source dot product
and the prior bounded kernel. **15,360 coordinate comparisons** cover basis,
arbitrary and all-max canonical selectors. The full twelve-test selected copy
module passes in optimized checked Rust, including its host-reference copy-lane
and frozen-registry comparisons.

These are universal kernel-checked algebraic/range models plus actual Rust
differentials and SBF executions. They are not an Aeneas/Rust/LLVM/SBF translation
or a whole-verifier equivalence theorem. Canonical field representation follows
the existing parser and field interfaces, unchanged by this patch. The image
gate, shifted ordinary rows, degree-q query batch and their causal boundaries
are untouched.

## Evidence and resources

Focused Lean leaves use the pinned 4.32.0 workspace and Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. Imported `CopyScatterNodes` source
and olean hashes are checked against the retained scatter evidence. The unchanged
`CopyTagSplit` leaf was compiled once to produce its **previously missing import
olean**, not to repeat its completed theorem audit without cause.

| Focused target | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|
| CopyTagSplit import artifact | 0 | 12.47 | 2,885,337,088 | 0 |
| CopyTagShared | 0 | 4.90 | 2,860,548,096 | 0 |
| CopyTagSums | 0 | 4.46 | 2,934,423,552 | 0 |

Only standard `propext`, `Classical.choice`, `Quot.sound` appear in the audited
dependencies; no `sorry` or new axiom is introduced. The retained logs contain
source and resulting olean hashes; the runner checks import provenance.

The NUC optimized Rust command exits zero in **33.02 s /656,148 KiB RSS**,
including compilation (tests 0.05 s). The SBF build exits zero in
**33.28 s /589,480 KiB**, with zero swaps. Build scopes use High5/Max7 GiB;
SVM uses High3/Max4 GiB; all use `MemorySwapMax=0`, jobs2 and existing caches.
No package-wide Lean replay or new prover execution occurs.

The selected ELF is **969,176 bytes**, +4,592 over the preceding bounded build.
Additional heap usage is **zero**: it reuses the existing 103-cell scratch and
59-node buffer. The direct-r10 audit reports 4,096 bytes for the emitted entry
and panic labels, with no new SBF stack warning; this is not a whole-machine
stack proof. No proof values, transcript messages, nonce or round is added:

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

Selected verifier SHA256:
`7f74c726967b29a37d679c3237b9abbe6c5945f6f52210875ad965928d57e562`.
Patched NUC copy-source SHA256:
`33fdefc5f4cbe6d3c3182f5abc11555d110c0d70b4c86dd548b89b6969d4fbbd`.
Generated entry-point SHA256:
`73343a877d574f2a1d171a574a091c23611560c69a3eed00de8652039fa01b8e`.
Runtime, Pool, Registry and Token are the same pinned comparison binaries
recorded in [results](tag-shared-results.json) and the
[preceding artifact map](tag-split-artifacts.json). No secret-bearing fixtures
or executable binaries are added to the repository.

## Reproduce and next decision

Locally, run `generate_tag_shared.py --check`, then the focused leaves with
`run_tag_shared_lean.sh LEAF ABSOLUTE_NEW_LOG` in order: `CopyTagSplit` (only
when its import artifact is absent), `CopyTagShared`, `CopyTagSums`. The split
import log path is `experiments/tag-shared-split-cache.log`, checked by the
runner. On the task-owned NUC copy after the preceding bounded-tag overlays:

```sh
bash experiments/run_tag_shared_nuc.sh prepare NEW_PREPARE.log
bash experiments/run_tag_shared_nuc.sh test NEW_TEST.log
bash experiments/run_complete_build_nuc.sh tag-shared NEW_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh tag-shared NEW_DIRECTORY
ASPIS_V8_TAG_SHARED=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

Here `experiments/` abbreviates this research directory's path. Remove only
`ASPIS_COMPLETE_MAX_FIXTURES` for the ordinary-body matrix. The preparer checks
the expected source hash before applying anything. `audit_tag_shared.py`
rechecks all archived results and source/Lean evidence without repeating suites.

Retain the shared kernel. A bounded source inventory also examined grouping
identical D inputs: 272 raw terms become only 270 nonzero grouped terms, with
maximum coefficient135, so that grouping alone is not a compelling next gain.
The next experiment is **specialising the remaining fixed tag-offset loop**
to remove runtime table/index interpretation, using the literal polynomial
as its reference and the existing raw-product/prefix bounds. Measure the
complete build against this shared version, including code-size and stack cost;
reject it if the larger generated code outweighs the removed interpretation.

The measured 1.2M margin is now larger, but universal CU coverage and matched-V7
parity are not established. Global recovery, full-view ZK and resource-bounded
FS remain separate unresolved gates. This arithmetic rewrite changes none of
their transcript laws and receives zero grinding credit; it is not a promotion
of V8's security or production status.
