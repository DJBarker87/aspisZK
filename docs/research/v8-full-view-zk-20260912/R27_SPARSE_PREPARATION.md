# R27: source-proved sparse preparation and reused arithmetic

2026-09-28; parent `7f1421807da7d7aeefebf1ba6d6355d794f81e3b`.
Branch `research/v8-r27-sparse-preparation-20260928`. Starts from the selected
R25 execution control, not any rejected R26 accumulator. Unchanged protocol,
proofs, T163, sparse G, transcript, wire layout, validation and heap.

## Complete executions

| Candidate | World 0 CU | World 1 CU |
|---|---:|---:|
| R25 selected control | 1,637,329 | 1,638,823 |
| Only required tensor groups | 1,626,085 | 1,627,579 |
| **Also shared blocks and alpha powers** | **1,620,236** | **1,621,719** |

The selected endpoint saves 17,093/17,104 CU against R25. Both genuine proofs
complete under the diagnostic cap, but **both still exhaust at the actual
1,000,000-CU cap**. No sub-1M result or global resource bound is claimed.
Malformed-final executions reject through checked errors at the diagnostic
cap; their 1M resource failures are not counted as checked rejections.

## Source-specific changes

The scalar consumer reads factors only at the 163 pinned support rows and
pivot 1023. The support's maximum is 478; its groups are exactly 0 through 29.
The pivot reads group 63. For each of the two tensors, omit groups 30 through
62: **66 full-field products** are genuinely not executed. The general
80-entry preparation and four-output terminal remain intact as references.

Then retain the pair-product blocks in the already allocated workspace at
fields 160 through 199. The two scalar block contractions reuse those blocks
instead of recomputing 24 pair products. Compute the four alpha square/cube
pairs once, avoiding another eight products. Workspace remains 531 fields;
there is no large array return or new on-chain allocation. This is identical
public arithmetic, not a profile/basis/privacy change.

The complete selected world-0 trace reproduces **1,620,236 CU** and checks
byte-identical `.text` between clean ELF and symbol artifact. It executes
1,513,633 instructions. QM31 multiplication entries fall from 2,269 to
**2,171**, exactly the proposed **98** removed products; exclusive multiplication
instructions fall from 342,679 to 327,881. Total saving is measured, not inferred
by multiplying an operation count by an assumed CU rate.

## Checks performed

- Actual modified scalar ordinary-plus-image result versus the retained full
  four-output computation: 256 arbitrary input vectors, including zero, one
  and maximal canonical limbs, plus both genuine 24-field public fixtures.
- Each arbitrary input also checks 47 required tensor coordinates against
  full preparation: **12,032 comparisons**. The 33 omitted cells are prefilled
  with one and checked unchanged: **8,448 poison-cell checks**. Scalar workspace
  is poisoned as well; no fresh-zero-workspace premise is introduced.
- Complete verifier host checks: both genuine proofs and all **3,281 wire
  controls**, including **3,280 checked rejections**, for both candidates.
- Stack-safe SBF compilation, complete diagnostic-cap acceptance and checked
  negative cases; unchanged 262,144-byte heap and simulated accounts.

Unchanged field-dot, dense-rank and full formal manifests were not rerun.
The focused ordinary gate replaces the unrelated dot gate for these stages;
no negative regression is deleted. Release/offline/locked cached builds use
bounded NUC scopes (5G/7G high/max), runtime and Lean 2G/3G, analysis 1G/2G;
all use MemorySwapMax=0 and TasksMax=128. No wallet, deployment or settlement.

The Solana skill's source/stack/whole-execution discipline decided acceptance.
Additional static review found only a low-severity `.unwrap()` advisory: the
private block read converts an exactly four-element slice, with fixed rounds
and 20-element caller slices. No critical/high issue was dismissed or account
check weakened. Static review is not a cryptographic audit; see
`R27_STATIC_REVIEW.json`.

## Formal and source boundary

`R27SparseRead.lean` proves the support-to-group bound and preservation of the
actual two-tensor entry expression from equality on precisely the retained
low/high coordinates. No field laws are needed for that read-set theorem.
Focused compile: **exit 0, 0.90s, peak RSS 798,432 KiB, swap 0**, cached Lean
4.31; both axioms reports are only `propext`, `Quot.sound`. Exact source SHA
and parent revision are recorded. The initial lightweight-import `Type*`
notation failure is retained, then fixed with an explicit universe; no cold
dependency build or broad theorem replay was started.

The separate eight-leaf first-relation boundary result is documented in
`R27_FIRST_RELATION_BOUNDARY.md`. It explains the omitted coefficient under
source-mapped premises; it does **not** establish universal source joint-image
compatibility, adaptive simulation, coherent pre-beta extraction or a shared-
oracle probability bound. Full privacy and soundness remain open.

## Reproduce and inspect

Selected workspace:
`/home/dombarker/project-offloads/aspis-r20-shared-blocks-20260928-a`.
All **182 source pins** are verified before each gate. Manifest SHA256:
`3c0741beddf4bc794a0e21fccc38fcfda7fd9aa227b0b2a3104d8121bd147f79`.
ELF SHA256:
`39d68001e62a43f6bc0c9e9834914c909097b4679fa3bc37fa029b9771a8c172`.

Run `stage_r27_sparse_prepare.py` from the R25
`aspis-r20-reduction-array-20260928-a` stage, then
`stage_r27_shared_blocks.py` from that candidate. Each requires exact pins and
a fresh output. Use `run_r23_full.py --stage STAGE --mode host|sbf|svm` in the
bounded scopes. Gate outputs retain legacy `r24-*` names, but source manifests
and ELF hashes distinguish every experiment.

Compact receipts, source deltas and logs are retained in
`evidence/r27-sparse-preparation`; audit with `tools/check_r27_evidence.py`.
Large raw traces/ELFs and retained keys remain on the NUC; keys are not bundled.
The next execution experiment should stay source-local and measured. This
checkpoint's 98-product reduction is not evidence that the remaining 620k CU
can be eliminated by a similar factor-count extrapolation.
