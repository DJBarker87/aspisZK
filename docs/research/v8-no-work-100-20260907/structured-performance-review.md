# Structured verifier CU rescue and basis-alignment pass

2026-09-08. Research branch `research/v8-no-work-100-20260907`.
Base: `9e57493dbba8fb01c50bd62f737f187006a33cb1`. This report and
its scoped source/evidence are committed together; no production source,
default, deployment, main branch or security claim is changed.

## Decision

The checked structured implementation consumes **1,888,165 / 1,889,539 /
1,889,695 CU**, without profiling calls. This is an actual complete execution
of the isolated research verifier on three fixed genuine masked-transfer
proofs, **not** a sum of microbenchmark estimates. It is about 74.2% below
the earlier dense prototype. Relative to the first quiet structured baseline
(2,150,511 CU, seed 1), the second pass saves another **262,346 CU / 12.2%**.

It still misses 1.4M by **488,165–489,695 CU before settlement**. Matched
complete V7/V8 transaction parity is not measured or established. This is a
substantial implementation improvement, not evidence to activate V8 and not
an impossibility result for the grammar.

A separate **not-selected** code-generation control, disabling blanket
overflow checks, measures **1,296,197 /1,297,648 /1,297,517 CU**, including
profiling. It passes at the normal 1.4M limit and rejects the same 27
malformed cases. This identifies substantial checked-arithmetic overhead;
it does not prove that blanket wrap semantics preserve every input path.
It is not used to claim CU parity or replace the checked endpoint.

Narrowing that control to **aspis-core only**, while keeping overflow checks
in the research callback and other packages, measures **1,325,336 /
1,326,821 /1,326,675 CU** with all the same controls passing. This localises
**567,456 CU** of the seed-1 profiled difference to core compilation.
Both controls remain explicitly unselected. This is a concrete next
range/refinement task, not another unspecified optimisation hope.

[Exact measured ladder](structured-performance-results.json),
[checked quiet SVM cohort](evidence/structured-best-quiet-svm.log),
[disjoint stage profile](evidence/structured-query-shared-svm.log),
[final checked build and stack diagnostics](evidence/structured-best-quiet-build.log).

## Measured progression

Every row after the dense reference uses the **same v2 proof bytes**, genuine
nonzero masks, cached platform-tools v1.54, selected arithmetic features,
LiteSVM 0.16 / Agave 4.2.1 and the same accounting boundary. Except explicitly
quiet rows, totals include diagnostic checkpoints. No local simulation sends
a transaction, uses an RPC service, or changes a pool account.

| Implementation | Seed 1 CU | Decision |
|---|---:|---|
| Previous dense reference, v1 transcript | 7,312,575 | Baseline, different transcript |
| Both structured families, no inversion batching | 2,347,169 | Dense costs eliminated throughout |
| Batch all 88 inverses directly in QM31 | 2,406,707 | **Reject regression** |
| Batch only 44 base-field inverses | 2,330,791 | Retain |
| Tower-norm inverses, mixed denominators, prepared primal folds | 2,154,055 | Retain |
| Quiet structured baseline with disjoint public-map scheduling | 2,150,511 | Second-pass comparison |
| Fuse z/XOR12 rows, fine profile | 2,104,160 | Retain |
| Cache points/affine pair and block-Horner semantic rounds | 2,015,250 | Retain after stack repair |
| Four-load packed decoding and bounded four-product gamma dots | 1,938,804 | Retain |
| Reuse gamma powers already constructed for point/OOD dots | 1,924,971 | Retain |
| Sum grouped mask coefficients before chord multiplication | 1,911,894 | Retain |
| Share signed chord/interpolant factors and prepared query alpha | 1,892,792 | Retain |
| Same checked implementation without profiling calls | **1,888,165** | Current measured endpoint |

A point-cache variant put 4,224 bytes in one SBF frame and failed at runtime.
It was **not** a successful CU result. The replacement boxes the cached
three-point array. Later checked builds have no observed >4,096-byte stack
diagnostic and execute all positive/negative controls. This is compiler and
runtime evidence, not a formal bound for every emitted stack frame.
The rejected build/runtime evidence is retained as `structured-shared-*`.

## What is changed, and what is not

### Structured transport through all four dual folds

`structured_weights.rs` keeps three MLE rows and the actual compiled
64-by-16 grouped mask in a compact description. The verifier never expands
either 1,024-vector. It calculates the affine correction from the needed
original entries (0 and 1 or 2), then computes four transported terminal
weights directly. The query-only 256-dimensional accumulator is injected
**after** alpha0. The four-entry carried image contribution remains inside
the relation. Query dual and final primal maps are deferred only because
they do not affect any intervening scalar, challenge, or transcript message.

The new fused row has block entries
`kappa*B[d] + kappa^3*B[d xor 3]` at coefficient bits 2/3.
It retains all four entries: no rank-one assumption or division by live
coordinate factors. The successor row keeps scale kappa squared.
The inactive scale remains 1. The mask rewrite moves the sum through the
already-defined linear chord functional; it does not drop honestly zero
residuals. It applies the actual source mask table, not fixture sparsity.

### Necessary, explicit research transcript version

The old implementation hashed **16,384 expanded public-weight bytes**.
It is impossible to omit their computation while pretending to hash the same
bytes. The v2 research path instead absorbs a **545-byte verifier-derived,
canonical functional description**, then the corrected ordinary scalar,
then a distinct image-gate profile label, and derives fresh nonzero tau.

The description consists of:
- fixed 43-byte version string and six profile/interpolation-axis bytes;
- 23 canonical QM31 values: z[10], row scales[3], chord[3], interpolant[2],
  both OOD points[4], gamma;
- 64 actual public row masks as little-endian u16 (128 bytes).

Statement/context binding, commitments, semantic messages, both sequential
OOD vectors, gamma, inactive claim and kappa are already in the prefix.
The description determines the same functional from those public inputs.
It is **not a prover-supplied hash or hint**. Ordinary scalar/weights are fixed
before tau; response0 still precedes alpha0. There are still three absorption
calls in this local binding step, with different framing and fewer bytes.

Thus the ideal algebra is comparable at identical challenges, but v1/v2
Fiat–Shamir proof bytes differ. V2 needs its own source/FS connection and
adaptive full-view hiding argument. No new positive security contribution is
assigned to this framing change or to work. The original 24 nonce bytes remain
and all measured honest nonces are zero; malicious selection powers remain
an obligation in the FS model.

The new v2 proofs have identical commitments and identical first 6,672 bytes
(417 fixed values before response0) to their v1 counterparts. Only the later
transcript-dependent relation/query evidence changes.

### Query and arithmetic details

- QM31 batch inversion using one inversion +261 generic products **regressed**.
  The retained path takes each element's actual tower norm down to M31,
  batch-inverts those M31 norms and reconstructs the exact extension inverses.
  Zero inputs/norms fail closed; legal zero coordinates of a nonzero extension
  element are supported. The 44 base fold denominators are separately batched.
- Four little-endian u64 loads unpack each exact 31-byte block. Every one of
  the 104 C1 /48 C2 limbs is still checked against noncanonical p.
  Column, helper and slot order is unchanged.
- Each gamma inner channel starts at zero and contains at most four canonical
  products; `4*(p-1)^2 < 2^64`. Explicit wrapping additions therefore equal
  integer additions under the parser/power-constructor invariants. Seven
  reduced chunks have their own smaller bound. No fifth product, negative
  term, or preexisting accumulator is smuggled into that proof.
- Query gamma powers reuse the same [1,gamma,...,gamma^28] table as the three
  point rows and two OOD batches. Host comparison also checks the prepared
  table equals the existing constructor.
- Opposite circle slots share the same base x/y products with signs; the
  reference's slot ordering and interpolation-axis choice are preserved.
  Prepared alpha/alpha-squared multipliers are shared by all 22 folds.
- The 28-coefficient semantic polynomial uses seven four-coefficient
  block-Horner steps. The omitted compact coefficient is still reconstructed
  from the prior claim; no semantic or relation boundary is bypassed.

## Mathematical and implementation evidence

### Semantic-terminal comparison and code-generation control

The selected V7 caller and this callback invoke the same literal terminal
function, with the same 3-by-28 projection. All ten selected arithmetic
feature aliases are enabled. A duplicate call with identical semantic
inputs in the same SBF build costs 543,600 CU, versus 545,550 for the first
call including projection/overhead. This does not reproduce the historical
407,973 number or justify booking its difference as a saving.

Source inspection found a separate build mismatch: this isolated manifest
sets `[profile.release] overflow-checks=true`; the selected workspace has no
release-profile override. The arithmetic files inspected are unchanged from
the historical selected revision, but the historical whole ELF/build/workload
has not been reconstructed in this continuation.
With only the diagnostic global `-C overflow-checks=off` change, the measured
semantic stage falls to **338,563 CU**, and the full profiled verifier falls
from 1,892,792 to 1,296,197 CU on seed 1. This is actual code-generation
evidence, **not** an established equality for all adversarial inputs.

The next useful proof-backed optimisation target is the reachable integer
arithmetic responsible for those removed checks. Canonical field operations
often already have exact bounds; broad core/index/length operations cannot
all be assumed to share that contract. Keep the checked build and existing
range-justified wrapping gamma kernel as the endpoint until that narrower
audit is complete. Source changes, not a blanket flag, can then remove only
the checks whose prerequisites actually follow from immutable decoded data.

The core-only control uses the explicit Cargo package override
`profile.release.package.aspis-core.overflow-checks=false`, not a source
edit or changed workspace default. It covers more core routines than the
proved four-product gamma range lemma, so that lemma alone does not justify
adopting the override. It also exceeds historical complete V7 figures before
adding settlement; no matched comparison is inferred.

| Artifact | What was actually established | What was not |
|---|---|---|
| `FusedRows.lean` | Complement block, tensor factor/update, exact kappa/kappa-cubed fusion under any linear transport | Translation of Rust carry kernel or full verifier equality |
| `BlockHorner.lean` | Generic quartic Horner step identity | Backend equivalence |
| `ArithmeticRewrites.lean` | Finite-sum chord distribution, canonical four-product prefix bound, exact modulo-2^64 prefix, seven reduced chunks bound | Every parser/power-constructor invariant in translated Rust |
| Structured host controls | All 16,384 weights and 64 terminal entries for adversarial coordinate profiles agree with dense reference; both interpolation axes | Universal adaptive soundness/ZK |
| Packed gamma controls | Canonical/zero/max-limb profiles, every one of 152 noncanonical positions, short-input rejection, exact comparison to source kernel | General malicious-transcript acceptance theorem |
| Existing v2 proofs | All three public-byte verifier outcomes and relation terminal weights agree with dense v2 reference | Full pool settlement |
| Final SBF controls | 3 positives at diagnostic budget; 27 malformed cases explicitly reject; 3 honest cases exhaust 1.4M | Worst-case accepted schedules or all transaction shapes |

Expanded SBF negatives cover fixed values, leaf/frontier tampering,
truncation, inactive claim, response0, final256, noncanonical fixed limbs and
appended data. Account data is unchanged in the local read-only simulation.
Explicit custom rejection is required, not merely exhaustion or a VM fault.
Finite test cases are not a proof of equality on all malformed inputs.
Sampler-exhaustion behaviour remains the existing fallible source path;
this cohort does not claim to have forced every sampler exhaustion branch.

Only the small changed Lean leaves were run, with cached mathlib:
`81a5d257c8e410db227a6665ed08f64fea08e997`, Lean 4.32.0.
No Aspis olean from concurrent main was imported. The common main workspace
was used only to access its pinned mathlib cache. Logs include axiom audits;
retained declarations have no sorry or new axioms. Standard logical axioms
are listed literally in the logs. One BlockHorner repeat recovered a missing
durable evidence artifact; no unchanged package-wide replay occurred.
See `structured-*-lean.log` and the evidence manifest for time/RSS/provenance.

The supplied basis-alignment archive was inspected before execution.
Its 32 full-dimensional fused-row checks reproduced its recorded output.
That Python count (328 vs169) is not mixed with the existing 91-product Rust
kernel count or treated as a CU forecast.

## Bytes, resources and remaining ledger

Maximum body, unchanged:
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282`.
Actual v2 bodies: **39,502 /39,606 /39,606** bytes. No new transmitted
claim, tau, nonce, padding or round. Account/instruction/lifecycle bytes
remain separate. Host dense committed columns are still 152 MiB plus salts,
trees and buffers. Verifier cache changes do not change this prover storage.

The final serial proving run (no concurrent task build) takes
**4.037744 /4.031301 /3.995573 seconds**, mean **4.021539 seconds** excluding
reusable setup (**1.384834 seconds**). Whole process: **13.49 seconds**,
**202,940 KiB /198.18 MiB peak RSS**, zero task swaps. This includes the
genuine masks and semantic producer, but no grinding/search. Three samples
are not a p95/p99 or universal latency guarantee. Synthetic public/proof
writes occur after the proving timer; network proof traffic is zero.
An earlier v2 generation overlapped compilation and is retained as evidence,
not used for the final latency comparison.

The security ledger is deliberately not numerically recomposed here:

| Event/interface | Change |
|---|---|
| Existing near-gamma supported bad-binding event | Its recorded exact rational ceiling is reused, not extended to extraction |
| Arbitrary accepted extraction failure / tuple-to-payment bridge | Unresolved term, no numerical value |
| Four carried relation repairs / image / shifted rho events | Checks retained; no second charge or mechanical subtraction from old inventories |
| Authentication | Same two root-bound trees and canonical opening evidence |
| Scalar/weight identity for new evaluation paths | Algebraic lemmas and differential evidence above; full translated source bridge still missing |
| FS lift, retries/nonces/forks/oracle queries | V2 transcript requires explicit resource accounting; zero work credit |
| Full-view masking/privacy | Separate unresolved simulator obligation; public descriptor is deterministic, changed responses still need coverage |

No “remaining release budget” or achieved global security bits are inferred
from a local subtotal. The wide-field/q23 controls and size allowances are
not changed.

## Reproduce and next decision

Use the task-owned NUC workspace recorded in `structured-performance-evidence.json`.
`experiments/run_structured_nuc.sh MODE NEW_ABSOLUTE_OUTPUT EXISTING_FIXTURES`
runs an offline bounded build, rejects stack diagnostics, runs the cached
local SVM cohort and records source/ELF/proof hashes. Modes preserve the
measured ladder; `best-quiet` is the selected checked endpoint.
`summarize_structured.py` independently reconciles integer CU deltas and
the body census from saved logs. A diagnostic overflow-control mode is
explicitly not the selected checked implementation.

Every heavy job used its own systemd scope, two compiler jobs and zero task
swap. No witnesses/secrets are logged or uploaded. No optimisation of C1
ownership, payment constraints, authentication, image/row checks, sampler
law, or proof-size cap was used to buy CU.

This pass does **not** establish that every optimisation is exhausted.
The next useful work is driven by the remaining measured cost, not by another
field/query sweep: resolve the semantic-kernel build/range discrepancy, then
profile its dominant checked arithmetic with exactly the same input tuple.
Only retain justified arithmetic changes that improve a full measured
verifier. Complete four-shape V7/V8 pool comparisons remain the final CU gate,
not a result obtainable by subtracting isolated kernels.
