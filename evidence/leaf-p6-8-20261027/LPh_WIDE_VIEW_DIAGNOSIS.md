# Stage 5: K023 is a harness modelling artefact

**Decision: the failed pass-through pointer assertions do not demonstrate shipped wide_view behaviour.** No shipped source is patched. The exact original failing harness is retained with a trace; full wide_view/carrier closure remains OPEN.

## Four diagnostic runs

| Run | Scope | Result |
|---|---|---|
| K027 | Actual wide_view on minimum10055-byte proof prefix, arbitrary non-inactive bytes, canonical zero inactive field, nonempty one-byte semantic/y1 carriers; compare pointers captured before the call and the folded-root range | PASS; exit0,37.999923687s,3863180KiB,swap0 |
| K028 | Same actual call, empty slices taken from live one-byte backing allocations, with pointers captured before call | PASS; exit0,43.160207823s,3868228KiB,swap0 |
| K029 | Tiny identity function returning its two input slices; no wide_view call. Test captured pointers, then fresh conversions of zero-sized arrays | Diagnostic FAIL; exit1,1.078000966s,218160KiB,swap0. Captured comparisons both PASS; fresh comparisons both FAIL |
| K030 | Exact inherited LPg_view1/K023 harness, now frozen-graph/offline checked with old-format CBMC trace | Diagnostic FAIL; exit1,13.112931378s,354480KiB,swap0. Reproduces both original pointer assertions |

The K030 rerun is for the previously missing counterexample trace; K023 was an assertion failure, not a timed-out/killed shape. No cap/timeout is raised. The frozen sources, graph, lock and all11 tool pins match. This is not a release replay.

## Exact trace and cause

K029 stdout lines2616–2620 record captured-pointer assertion.3/.4 SUCCESS (source line16), fresh-ZST assertion.1/.2 FAILURE (line17). The trace chooses one nonzero word when coercing the zero-sized array to a slice, carries that exact word through the identity function, then chooses another nonzero word for the fresh array-to-pointer conversion. One concrete pair is18446744073709551614 and18446744073709551615. These are rendered INVALID-65535 by CBMC; neither pointer is dereferenced. Capturing and reusing the same slice pointer succeeds. Its extra fmt reachability sentinel is retained, not misreported as a shipped property failure.

K030 reproduces original semantic assertion.8 (source line10) and y1 assertion.7 (line11). The returned wide_view fields have **exactly their incoming slice data words**, through each Result/View copy. The later fresh zero-sized-array conversions choose independent nonzero words. The failure compares different conversions, rather than testing preservation of the given Slice carrier. The original raw CBMC results also contain35 Kani reachability sentinels; “37 of360” is not37 shipped failures. The two user assertions are the two pointer comparisons.

Complete K030 trace:53,293,707 bytes,41,987 lines, SHA256
`078bb4c0549350747b1493576c9c833cc57309b880288f66885971ebb1f9c410`.
It remains at the host path in LPh_K030/full-stdout-reference.json. To respect the local disk/no-large-artifact rule, the committed stdout.pointer-excerpt.log contains verbatim relevant SSA blocks and original full-log line coordinates. Full selected assertion traces begin at original stdout lines27731 and32401. The full trace is not rewritten or deleted on the host.

The frozen production caller supplies nonempty logical semantic/y1 buffers (13831/928 bytes); K023 deliberately used zero-sized diagnostic arrays. The source itself assigns `semantic` and `y1` directly in candidate.rs:79–80. The diagnosis is also consistent with Rust's pointer API: pointer equality compares addresses, and zero-sized allocations can be represented without an accessed byte allocation ([core::ptr documentation](https://doc.rust-lang.org/core/ptr/)). The empirical identity-function trace, not a general claim about pointer provenance from addresses, is decisive here.

## Limits and next stage

The diagnosis stage is CLOSED. The entire candidate::wide_view leaf is OPEN: arbitrary full proof carrier ranges, lifetime/borrow/frame interpretation, exact native/model Slice association and actual caller installation still need a joint bridge. Passing a zero-length diagnostic or an empty-byte equality is not promoted to that full result. No new trust item, precondition on the actual game, or cryptographic assumption is introduced.

Budget STOP:30/30 Kani and60/60 Lean. No further prover run is permitted under this allocation.
