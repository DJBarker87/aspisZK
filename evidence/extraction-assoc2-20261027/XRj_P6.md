# New prepared_claim per-iteration Kani evidence

Ten new optimized runs, sequentially admitted; no extraction or shipped change.
Nine PASS, one TIMEOUT; neither whole prepared_claim harness shape is rerun.
All exact commands, source snapshots/hash pins, revision, exit/wall/RSS/swap,
limits and admission logs are retained in XRj_K001 through XRj_K010.
The unchanged S2W runner checks 6G/8G/Swap0/Tasks64 inside each scope.
Cargo dev profile opt-level3, debug0, overflow checks true; jobs1, offline.

| Runs | Domain and result | Limitation |
|---|---|---|
| K001–K006 | Six separate scalar-branch projection snippets; l arbitrary in0..28, four canonical QM31 limbs arbitrary; PASS, including cover l=28 | Sparse diagonal fixture: every populated claims/extra/before entry and y1's selected scalar are the SAME x; other slots zero. This checks equality of match/if source snippets on that domain, NOT arbitrary differing branches, actual Verified borrowing/decoder composition or full scalar selection. |
| K007 | One powers-loop store/index/multiply body, i0..27, arbitrary canonical base-field-only p,x; attempts commutation of the one product; CBMC90s TIMEOUT | No arithmetic conclusion accepted. This is a single-iteration shape, not the retired whole loop. No unchanged retry or cap increase. |
| K008 | One real EbyKDot push from new, arbitrary canonical base-field-only E and zero K; PASS, finish zero | Single term, sparse E, zero scalar; no arbitrary running Dot/history/count proof. |
| K009 | One real EbyKDot push from new, E::ONE and arbitrary canonical full K; PASS, finish E::from_qm31(K) | Single term and unit E only; no general multiplication or count bound. |
| K010 | One outer claim-fold transition, arbitrary canonical base-only old/part and zero coefficient; PASS, unchanged old | Sparse arithmetic domain; no seven-part accumulation or oracle effects. |

Source projection is verifier.rs:59's actual match versus
XRe_reference.rs:11's if expression, on explicit projected arrays. It does not
call the full shipped private function. Dot checks call the actual public
EbyKDot. No digest stub, Kani contract or alternate source body is installed.
`XRj_power_step` is a source-stage test plus a proposed algebraic assertion;
its timeout is retained, not called a source counterexample.

Inputs have concrete zero/index0 witnesses. Six scalar covers reach index28.
This is local bounded-domain non-vacuity, not a joint actual-top witness.
Full P6 remains OPEN for all twelve leaves. No actual-top premise is removed.
Aggregate: wall178.8728439739789s, peak1050348KiB, swaps0.
