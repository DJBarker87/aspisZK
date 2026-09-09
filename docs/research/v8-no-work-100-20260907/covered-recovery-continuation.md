# Covered recovery: retain alternative C1 candidates

Research parent: `bc23dfeb647320c4fbf09012cd92da1a6a5fa95a` on
`research/v8-no-work-100-20260907`. All new compilation and arithmetic checks
ran on the NUC, as requested. No verifier, transcript, production, field,
domain, query count or proof-body change.

## What changed

The next recovery theorem must allow a valid alternative candidate, not
require the prover's claims to describe one particular dominant C1 decoder
output. A fixed mixed-C1 construction demonstrates why that distinction is
necessary. The conditional relation-suffix event “accepted and wrong about
the dominant C1” can have probability at least approximately
`2^-87.727713036684`. This is **not a payment forgery**: the control does not
execute a semantic prefix or establish that either candidate is a valid
payment. It refutes an overstrong intermediate target.

Three focused Lean leaves supply the replacement analysis objects:

| Family | Literal membership | Maximum cardinality | Earliest fixing point |
| --- | --- | ---: | --- |
| Quotient | Natural1024 Q agrees with arbitrary received R on at least 9,558 complete fibres | 99 | Once R is fixed, before kappa/tau/alpha; not before gamma |
| Original C1 | 26 original-code messages jointly agree with fixed C1 on at least 38,228 original symbols | 100 | C1 commitment, before lambda/chi and adaptive C2 |

The new C1 theorem additionally proves that any actual late 26+3 tuple with
that much own support projects into the early family. Every member has
base-field coefficients when the fixed received C1 values are in the base
field. These are exact selected-encoder results, not a freely supplied
projection equation or per-lane decoder-membership assumption.

Neither finite family is an efficient list decoder. Nor does a represented
batched quotient automatically produce a represented component tuple.

## The falsified target and its repair

The [mixed-C1 control](mixed-c1-control-review.md) fixes a minority set S of
16,535 complete fibres before every challenge. C1 lane0 is its indicator;
the other C1 lanes and the three helper words are zero. Thus the helper
curve still has degree at most two. The zero tuple p0 has the dominant
245,609-fibre support. The alternative tuple p1 has the constant-one
polynomial in lane0 and agrees on S.

Claims and both sequential OOD answer vectors describe p1. For any legal
no-pole chord prefix, its interpolant is 1, its quotient is zero, and the
actual virtual received word is `(indicator(S)-1)/L`. The affine-corrected
ordinary relation, shifted kappa rows and image gate all admit the causal
zero-quotient/zero-final suffix when queries lie in S. The claims disagree
with p0; that error remains a degree-at-most-28 component-claim polynomial,
not the degree-two helper curve.

Using the nonzero four-slot fold polynomial outside S, at most three alphas
can make this final not far under the current 15,334 cutoff. Consequently
the following is a **conditional lower bound**, not a new security ceiling:

```
((k-3)/k) * choose(16535,22)/choose(262144,22), k=(2^31-1)^4.
```

The exact rational and conditions are in
[mixed-c1-control-ledger.json](mixed-c1-control-ledger.json). No OOD challenge
is forced; a concrete permissible no-pole prefix and the conditional scope
are explicit. The optimized F31 control exhausts its stated fixed causal
strategy, not all adversarial strategies. Its rates are not extrapolated to
QM31. The full-profile lower bound comes from the symbolic construction.

The legitimate repair is to retain possible alternative original-code
tuples, connect at least one to the actual semantic claims, and validate its
decoded witness. Here p1 has 66,140 matching original symbols and so is not
lost by the 38,228-symbol family floor. No new verifier message or check is
proposed merely to force the dominant tuple to be the only target.

## New theorem and dependency map

| Endpoint | What it establishes | What it does not establish |
| --- | --- | --- |
| `QuotientFamilySelected.candidateFamily_ncard_le_99` | Exact old `CandidateFamily univ R 9558` has at most 99 members, for arbitrary R | Image/row validity, component recovery or executable enumeration |
| `EarlyC1Family.family_card_le_100` / `mem_family` | Unfiltered, C1-only family has at most 100 members and exact membership | Acceptance implies family membership |
| `EarlyC1Family.actual_late_projection_member` | Literal `received29 c1 c2` own-support membership implies early C1-family membership | Existence of a late tuple for every accepting quotient |
| `EarlyC1Family.member_is_base` | Every member descends using its own support and actual encoder commutation | Canonical parser/source refinement or decoder runtime |

The quotient proof reuses the selected four-lane inverse and final-code
overlap cap 255. The C1 proof instead reuses the original-code overlap cap
1,024 **symbols** and exact 26+3 lane projection. These different overlap
caps are not interchangeable. The inherited Johnson inequality proves the
cardinalities without enumerating a concrete field or message universe.

V7 source is pinned at `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The old filtered C1 list is not silently substituted for the new family.
The existing semantic/copy causal machinery is reusable, but its old
183-link registry and old witness endpoint do not certify the current
weighted 136-link selected relation.

## Total extraction accounting

Fix a specific bounded extractor E. Let A be complete repaired-verifier
acceptance, X mean E returns any witness passing the literal validator with
independently authenticated context, Access mean its specified access stage
succeeds, and V mean the mathematical early C1 family contains a candidate
whose canonical semantic projection passes that validator.

The following disjoint bookkeeping retains all accepted failure mass. It is
an event definition, **not a proved quantitative extractor theorem**.

| Precedence | Event | Remaining obligation |
| --- | --- | --- |
| 1 | `A AND NOT X AND NOT Access` | Actual root-bound access, authentication, replay, missing/cached/advance responses, fuel and source coupling |
| 2 | `A AND NOT X AND Access AND NOT V` | Accepted relation/semantic execution implies a suitable component-family candidate and valid payment, or a charged bad event |
| 3 | `A AND NOT X AND Access AND V` | Bounded list recovery and successful literal validation, including resource/parser failures |

A successful alternative witness contributes zero even if it is outside a
chosen analysis family. Provider `none`, a missed radius cutoff, or a wrong
dominant tuple does not become a witness-extraction failure by definition.

Within class 2, off-quotient-family finals have the inherited ideal
[104.592-bit suffix theorem](adaptive-tail-continuation.md), under its actual
causal game's hypotheses. Represented finals still require a joint
image/ordinary-row argument, then a quotient-to-component argument retaining
gamma's degree-28 error and C2's degree-two curve. The new early family
fixes those **projected C1** candidates before lambda/chi; it does not move
adaptive C2, a gamma-dependent quotient, or a post-alpha final backwards.
Correct scalar acceptance with failed pointwise checks remains covered by
the actual shifted degree-q rho/repair events, not discarded as impossible.

The [payment/source audit](covered-extraction-obligations.md) identifies a
concrete subsequent deterministic bridge: selected weighted Copy LogUp rows
to the literal aliases used by the checked payment endpoint. Inactive
zero-weight slots still occur in cross-multiplied denominator factors; their
poles cannot simply be omitted. The existing amount/note/path/output/append
leaves are useful same-table prerequisites, not a completed universal
residual-to-validator theorem.

## Ledger and cost boundary

[covered-recovery-ledger.json](covered-recovery-ledger.json) keeps unproved
terms symbolic. The new cardinality and descent theorems have no numerical
failure term. The old off-family suffix bound is reused unchanged; its
query term is not multiplied by 99 or 100. A future represented-family union
must charge the single actual rho batch and later relation repairs once,
not sum independently duplicated complete suffix bounds. This composition
has not been proved in this continuation.

There is no new global numerical budget certificate or justified numerical
allowance for all remaining terms. The historical 396430 inventory is not
imported. Full-view ZK and a resource-bounded FS lift remain separate; nonce
selection, retries, oracle prequeries, forks and extractor runtime are not
free or credited as work-based security.

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

New verifier operations and transmitted bytes: zero. No new CU, prover-time,
SBF, or full-transaction measurements were run. The retained performance
measurements are unchanged. A family-cardinality bound supplies neither
list-decoder runtime nor measured peak RAM.

## Focused NUC evidence

Lean 4.32.0 pin `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
Mathlib pin `81a5d257c8e410db227a6665ed08f64fea08e997`.
The fresh overlay reuses hash-checked pinned imports without rebuilding the
native package cache. No compilation ran on the laptop.

| Target | Exit | Wall | Peak RSS (KiB) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `QuotientFamilyCore` v2 | 0 | 2.96 s | 6,684,452 | 0 |
| `QuotientFamilySelected` v1 | 0 | 3.32 s | 6,835,928 | 0 |
| `EarlyC1Family` v2 | 0 | 3.00 s | 6,712,524 | 0 |
| Mixed control optimized compile v3 | 0 | 0.46 s | 143,728 | 0 |
| Mixed control execution v3 | 0 | 0.00162 s internal | 2,640 | 0 |

Lean jobs ran serially with MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPUQuota 200%, `-j1 -M9500`; Rust used 1/2 GiB high/max,
no swap and optimized overflow-checked compilation. The runner's exact
native `lean -R ... -o ...` command and environment are recorded in each log;
it consumes the pinned `lake` workspace/cache, not a cold dependency build.
The three leaves' 16 named audits use only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorry` or new axiom is retained.

Failed preflights are retained: a missing namespace, concrete finite-family
elaboration exceeding its recursion limit, and Rust path/edition setup.
The family issue was fixed with a generic finite-membership interface and
an opaque family boundary, not by increasing limits or reducing an enormous
message universe. No unchanged full regression was repeated.

Recheck retained evidence without recompiling:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_quotient_family_evidence.py --check-recorded
```

For a changed focused leaf only, after a source/provenance preflight, use a
fresh tag with the recorded remote runner:

```
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-masked-tail.m4IQIB/run_quotient_family_nuc.sh /home/dombarker/project-offloads/aspis-masked-tail.m4IQIB EarlyC1Family NEW_TAG'
```

See [family evidence](quotient-family-evidence.json) and
[transfer receipt](quotient-family-transfer.json) for exact source/output
hashes and failed snapshots. Cache-byte provenance is not a new proof of
the compiler or a replay of every imported module.

## Decision

Keep QM31 q22 as the primary research design. The new falsifier changes the
extraction target, not the verifier or profile: recover a suitable valid
candidate rather than prove uniqueness of the prover's chosen interpretation.
The two kernel-checked families provide the correct causal containers for
that work. Global accepted payment extraction, efficient list access,
source/FS and full-view privacy remain open.

The single next formal experiment is to connect the literal 99-member
quotient family to the existing image/shifted-row first-discrepancy game,
then attach the **one shared** actual query/repair suffix. It must permit
post-alpha final selection and retain the image-and-row-correct component
remainder explicitly. Success would remove represented invalid-image/row
candidates without reviving the disproved wrong-dominant-C1 target; it
would still not prove the component remainder recoverable.
