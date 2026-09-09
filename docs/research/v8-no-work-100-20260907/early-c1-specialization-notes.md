# Early-C1 specialization: explicit finite-instance repair

Research base: `15e73e9fdf529a0d0ab46353b98bccaf029bf4f5`.
Status: **the exact optional identification and late-C2 projection are
kernel-checked**. The existing `earlyC1` definition, support definition,
encoder, domain and 245,609-fibre threshold are unchanged.

## Completed causal-mathematical milestone

`EarlyC1Specialization.identify` proves the previously missing application:

```text
245609 ≤ (support fibreEncode (receivedFibres received) p).card
  → earlyC1 received = some p.
```

`EarlyC1LateProjection` then constructs the actual-width combined oracle
from fixed 26 C1 lanes and arbitrary three late C2 lanes. It uses the existing
V7 `c1LaneIndex` and fibre-major index map. For any 29-message tuple with at
least 245,609 complete fibres of joint own support, the first 26 messages
equal the pre-existing optional object defined from C1 alone. Consequently:

- Any two qualifying late tuples, even for different arbitrary C2 words,
  have the same C1 projection.
- If that C1-only object is `none`, no such qualifying width29 tuple exists.
  This does not remove or bound all accepted/provider-`none` executions.

The supplied tuple may be selected after earlier challenges and C2. The
theorems do not treat that selection as early; they identify its C1 projection
with a separately defined C1-only object. They do not assert that a
qualifying tuple exists on every execution. In particular the near-gamma
small-Good branch and the far/uncovered regimes remain visible.

## What the explicit diagnostic establishes

The ordinary displays hid two different `Fintype (Fin 262144)` instances:

- `earlyC1`, the concrete support/overlap types and the current import
  environment use
  `SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat (SimplexCategory.mk 262143)`.
- `c1_margin`, compiled with the smaller arithmetic imports, uses
  `Fin.fintype 262144`.

Thus the previous direct theorem application asked definitional equality
to reconcile different finite enumerations inside `Fintype.card`, despite
identical pretty-printed mathematical statements. The new diagnostic reads
these stored types without applying the failing specialization: exit 0,
3.75 seconds, 5,506,695,168 bytes peak RSS and zero swap. Its full output is
`experiments/early-c1-specialization-v1-types.log`.

The successful repair transports the cardinality proposition by
`Fintype.card_congr (Equiv.refl (Fin 262144))`, with both finite instances
supplied explicitly. It preserves the carrier, encoder, support, threshold,
optional object and intended theorem. It does not normalize either
enumeration, switch to a new matching count, assume a populated option or
increase a resource cap.

The intermediate concrete `rw`/implicit-instance applications still exceeded
the guard; they were preserved rather than rerun unchanged. The retained
implementation first proves an abstract-carrier `Eq.mpr` transport, then
uses a named alias of the *actual* inherited instance and fully explicit
applications. The two margin proof values retain inferred types (`def`
rather than `theorem`); Lean's style warnings are recorded. Both are kernel
proofs of propositions, audited with the same standard axioms as the final
theorem. No warning is treated as proof success without an exit-zero leaf.

## Intended effect and boundaries

The endpoint identifies any supplied 26-column message tuple with at least
245,609 complete matching fibres with the existing `earlyC1` object defined
from the received C1 word alone. No C2 word, lambda, chi, gamma or later
provider result is an input to that object. The `none` branch is retained.

That is a deterministic mathematical fixing result conditional on the
stated support. It does not prove that every accepted proof produces this
support, recover an oracle from a Merkle root, implement a bounded extractor,
establish base-field descent or validate a payment witness. C1 authentication
and access/timing remain their own source/game obligations. No new error
probability, security bits, proof messages, body bytes or CU are introduced.

## Provenance

The new runner pins the complete 78-module Aspis source closure against the
research revision and verifies its byte identity with the read-only cache
workspace before/after a successful leaf. It retains the existing checked
V7 encoder/overlap cap and all prior research objects. The type diagnostic
records main at `d851f36bc0ee41459156e125aaa04e4a0941ac70`, Mathlib at
`81a5d257c8e410db227a6665ed08f64fea08e997`, and Lean 4.32.0. It does not
import newer unrelated K1 work.

## Theorem and evidence map

| Retained declaration | What it establishes |
|---|---|
| `EarlyC1InstanceTransport.transport` | Cardinal-margin transport between arbitrary finite instances of the identical carrier; no enumeration |
| `EarlyC1Specialization.before_margin`, `source_margin` | Explicit specialization to the stored C1 instance, with the checked arithmetic premise applied |
| `EarlyC1Specialization.identify` | Exact existing `earlyC1` option equals any qualifying C1 tuple |
| `EarlyC1LateProjection.received29_c1`, `fibreWord29_c1` | Exact first-26 lane and complete-fibre restriction |
| `EarlyC1LateProjection.late_projection_identifies` | Width29 own support implies identification of its C1 projection |
| `EarlyC1LateProjection.independent_of_late_C2` | Qualifying projections coincide across arbitrary late C2/tuple choices |
| `EarlyC1LateProjection.none_excludes_qualifying_tuple` | Explicit absent-option branch excludes qualifying tuples, not all accepted executions |

The reused V7 encoder cap is source SHA-256
`78571066d66be07ccfbd526d36be9515be60920cbecc416da467fff44ba1f6e3`
(`V7C1ConcreteProjectionBinding.lean`); the lane-index source is
`a4d7b012f96a5de8f620bceffcaab0eaecbdb3469f84720b3658ab6890f9007b`
(`V7ExtractedLaneWords.lean`). The existing exact four-slot bridge and optional
support lemmas are consumed from their pinned checked caches. This is a
kernel-checked mathematical/source-shaped result, not translated Rust.

| Focused run | Exit | Wall | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| `specialization-v1-types` | 0 | 3.75 s | 5,506,695,168 | 0 |
| `specialization-v2-margin` | 137, guard | 11.47 s | 7,644,561,408 | 0 |
| `specialization-v3-generic` | 0 | 0.72 s | 1,282,588,672 | 0 |
| `specialization-v4-margin` | 137, guard | 10.51 s | 7,811,596,288 | 0 |
| `specialization-v5-partial` | 0 | 2.95 s | 5,507,350,528 | 0 |
| `specialization-v6-margin` | 0 | 8.00 s | 5,509,464,064 | 0 |
| `specialization-v7-identify` | 0 | 3.23 s | 5,647,155,200 | 0 |
| `late-projection-v1` | 1, missing noncomputable keyword | 3.08 s | 5,496,160,256 | 0 |
| `late-projection-v2` | 0 | 3.93 s | 5,656,756,224 | 0 |

Every filename in this table has the prefix `experiments/early-c1-` and
suffix `.log`. Guarded failures were not repeated unchanged or given larger
limits. The final specialization runs at `maxRecDepth 80` and
`maxHeartbeats 2000`; late projection uses the same recursion bound and 5000
heartbeats. All jobs used `-M7000` plus the separate 7-GiB aggregate-process
guard. The one-second guard sampling explains the small measured overshoot
on failed runs. Only `propext`, `Classical.choice`, `Quot.sound` occur in the
retained result audits; no new axioms or `sorry` are used.

Final successful sources were not edited after their recorded checks:

| File | Source SHA-256 | Olean SHA-256 |
|---|---|---|
| `EarlyC1InstanceTransport` | `2476cc09c9eabf19b0ff8fed798d997128306a67a831eb699785ecf3f9c102e1` | `4137cb43679b6ac083f6d13f37b242745c3e793263074dd23e2470498e7fb13f` |
| `EarlyC1Specialization` | `60e666c4d32774496c4f768524e4ef097bd82e40634ce01a9ba23aa0672bb7eb` | `0d59fb1f577b7e63b8fa907e1616f2169350c209781b4cb710b2b8e1c29e3ab1` |
| `EarlyC1LateProjection` | `0abdc0ec046d47952cbc156f336c48ac35e41498192720ccab7fc627eec00c2b` | `0529d8557f744e416cbc9b3f0855b28611afddbde4cca9ae22b54c89aa3e1495` |

The final runner SHA-256 is
`0e772bc48fee9b203fcedbc63fc52d1757dc29def428dba74b9ef4bae2da1fcb`.
With the pinned prior caches available, replay only the relevant changed
leaf, using a new nonexisting log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_specialization.sh \
  /tmp/c1-transport-new.log EarlyC1InstanceTransport
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_specialization.sh \
  /tmp/c1-specialization-new.log
bash docs/research/v8-no-work-100-20260907/experiments/run_early_c1_specialization.sh \
  /tmp/c1-projection-new.log EarlyC1LateProjection
```

The next C1 obligation is to supply the actual accepted-execution tuple and
its own support, with source authentication/replay accounting, then connect
the now-fixed C1 projection to base descent and the early semantic/copy
constraints. The theorem above does not manufacture this input. This run
does not expand field descent, run SBF, change production, or claim a global
probability/cost certificate.
