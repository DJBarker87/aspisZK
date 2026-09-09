# Causal authentication, actual C1 trace, and the selected payment endpoint

Continuation from `bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`.
The executed Rust controls were first published independently as
`4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e`, without unfinished Lean drafts.
Main, production programs, deployment defaults and the measured SBF verifier
remain unchanged. Concurrent main work and untracked proof leaves are preserved.

## What materially changed

**Authentication now has a constructed resource-bounded model, not just an
assumed event inclusion.** [EarlyC1OracleMachine and EarlyC1OracleGame](early-c1-oracle-review.md)
define the actual sequence of cached/fresh calls, returned log and final cache.
They derive the whole-domain first-unresolved-target event from those objects
and reuse V7's budgeted causal counting theorem and exact 256-to-208-bit
projection. For positive call depth the bound is `Q/2^190`, for Q fresh calls
after the fixed prefix. This is conditional on the ideal full-output oracle
law; it is not a global security figure or a theorem about SHA-256 itself.

Cached calls do not spend the fresh-call budget, but still occupy finite call
depth. The strategy sees all 256 bits, including the truncated tail. Fresh
budget exhaustion has an explicit abort result. Actual provider replay,
restoration, fuel and challenge-mismatch outcomes still need their separate
source coupling; a depth-zero `halt` is not automatically a provider-fuel abort.

**The corresponding source control now runs on one genuine payment.**
The [actual-answer recorder](early-c1-trace-review.md) freezes 1,051,764 returned
hash answers before lambda/chi and checks all 22 accepted openings against the
same early C1 root and the actual verifier call's recorded paths. It performs
no resolver hash calls and does not read producer coefficients. Raw prefixes
and salts remain in memory. This is a differential interface check, not the
universal Rust-to-model coupling or a replay extractor.

**A proposed deterministic endpoint implication is genuinely false.**
The [selected transfer test](selected-transfer-zero-review.md) constructs two
zero-output tables outside the honest compiler. Each satisfies all 18,089
literal residuals, including 3,803 padding residuals, and all 1,024 selected
Boolean composition probes, yet the current selected compiler rejects it.
Decoding succeeds; the stricter validator is the failing step. A mathematical
tuple with correct point claims therefore does not yet imply acceptance by
that chosen witness endpoint.

This is not a demonstrated accepting PCS/FS/pool transaction or absence of
another valid witness. The older generic payment relation permits hidden zero
values and has a different path model. It cannot silently replace the selected
pair/forest/compiler endpoint to make this implication true.

`SelectedTransferPositive` reuses the established V7-derived range/no-wrap and
selected copy/conservation results. It proves that adding the proposed single
product-inverse residual makes all three decoded amounts strictly positive,
less than `2^30`, exactly balanced, and safe for the checked u32 output sum.
This is a meaningful repair prerequisite, **not an installed verifier check**.

## Relation/source bridge

The [interleaved chord development](interleaved-chord-review.md) consumes the
previous exact natural-basis image and projection results. It constructs the
total coefficient reconstruction and its derived covector transpose; the
ordinary prior must use this total natural map even on invalid images.
The image premise belongs only in its evaluation/correct-code theorem, not
in the definition of the map. The companion current-source evidence records
which focused leaves passed. No optimized Rust carry-loop correspondence,
actual point-functional/transcript constructor or full verifier theorem is
inferred merely from a linear-map identity.

## Total accounting: accepted checked-extraction failure remains the target

Let A be acceptance by the intended repaired complete verifier and X the
specified bounded extractor returning a witness accepted by the selected
payment/context/transition predicate. The goal is still `Pr[A AND NOT X]`.
The following is an obligation map, not an already-proved partition or a list
of probabilities that can simply be added:

| Actual stage/class | New evidence | Remaining accepted mass/obligation |
|---|---|---|
| Accepted C1 opening differs from early word | Existing deterministic binding alternative; new causal target probability | Couple actual calls/prefix/path to model; charge shared raw collisions and total resources |
| Prefix C1 has a qualifying recovered projection | Existing early identification and late-C2 independence | Obtain/extract it within declared resources; defaults are not authenticated samples |
| Near-regime image/point/row binding | Earlier conditional near-gamma and repaired causal row results retained | Instantiate on the same source word and actual functional/encoder; near membership is not X |
| Outside/far/no-provider-candidate executions | No branch discarded | A quantitative recovery bound or a checked extraction route, including successful out-of-radius recovery |
| Scalar acceptance but pointwise checks fail | Degree-q rho and sequential repair lemmas retained | Source-correct composition; no duplicated four-round repair charge |
| Recovered current selected residual-zero table fails strict endpoint | Concrete zero-output falsifier | Integrate justified positivity repair or prove a legitimate equivalent endpoint; never assume decoder/compiler success |
| Replay abort, fuel, missing response, cache/advance mismatch | Still explicit failures of the chosen extractor | Actual replay scheduling, resource accounting and success/failure coupling |
| Canonical parser / authoritative context / settlement | Existing local controls and proof slices | Full deterministic source refinement, not an invented small error term |

The shared raw-208 collision term remains resource dependent. The new target
bound is one whole-domain event, not 22 copies and not a 104-bit birthday-work
probability. Earlier near/image/row/query bounds overlap; their four relation
repairs are not charged again. The old 396430 inventory is not imported.
Unproved global terms and remaining global allowance remain `null` in the
machine-readable ledger. There is no completed 100-bit certificate here.

## Cost, privacy and decision

The installed research grammar still has

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

Only optional host instrumentation was added to the callback/producer. The
one recorded proof is 39,502 bytes, not a maximum-size stress proof. Its
7.96-second instrumented execution/664 MB RSS is not the previous NUC proving
benchmark or a new CU result. The previous worst measured complete total is
1,047,041 CU under its frozen four-shape experiment, not a universal cap.

The positivity control reserves existing row1014/column3 for
`u=(recipient*change)^-1`. It proposes one cubic residual at the already-used
conservation row and can fit the existing packed-lane/body model. It consumes
one relation-free mask coordinate (3,803 to 3,802), needs updated static
layout/profile binding and hiding arguments, and introduces real prover and
verifier arithmetic. Full counts and source locations are in the endpoint
report. No CU saving or parity is assigned to this unimplemented control.

There are no new public messages in the executed instrumentation. A future
inverse cell remains private committed witness data, but that observation
does not prove full-view privacy after changing mask dimension or relation
responses. Adaptive hiding and resource-bounded Fiat–Shamir remain independent
unfinished requirements. All oracle claims here are classical; no quantum
security claim or positive work/grinding contribution is introduced.

**Decision:** keep the q22 architecture as the primary research route, without
promoting it to production. The next decisive endpoint experiment is a
research-only installation of the product-inverse check and corresponding
mask/layout update: the genuine positive transfer must still pass, both
zero-output controls must fail through the actual selected semantic producer
and repaired verifier, and byte/hiding/CU consequences must be measured or
proved before retention. In parallel, the accepted uncovered recovery and
source-to-oracle coupling remain essential; this local repair does not close
either one.

## Reproduction/evidence

The focused runners, exact source/olean hashes, standard-axiom audits, exits,
wall times, RSS and zero-swap records are linked by
`oracle-endpoint-evidence.json` and checked with:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_oracle_endpoint.py --check-recorded
```

Imported V7 lazy-oracle dependencies use an explicit immutable
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5` cache-source pin; the research
dependencies retain `bc945367`. This was necessary after the preflight caught
a changed V7 transcript-count dependency. V7's numerical q16 caps are not
reused. Other focused closures retain their recorded pins. No cold Lean
dependency build, package replay, generated aggregation or SBF rebuild ran.
