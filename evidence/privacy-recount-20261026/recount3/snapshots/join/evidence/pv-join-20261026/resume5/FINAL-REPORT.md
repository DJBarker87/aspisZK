# pv-join5 final report

Branch `codex/pv-join-20261026`, resume base `8eba145a71`. **Target not yet established.**

## Proved, measured, and open

**Op121 remains OPEN.** Direct Charon extraction succeeds; Aeneas rejects compiler-generated Drop, then fails in loop-context collapse after only unused FnOnce methods are made opaque. No backend/source repair. The closure-free owned radix-four reference extracts and its 29 declarations compile. Full canonical-domain equivalence and the smaller sum3 equivalence both time out at240s; neither is retried unchanged or claimed as a proof.

`PV_Join_CurrentPolynomialCanonical5.polynomial` (38090) proves every successful `host_sumcheck.interpolate` output canonical for `PV_Join_PublicCaller.selected`, on arbitrary raw evaluation values. Scalar/complex/quartic parser invariants, reducer invariants, canonical arithmetic and array/loop preservation are green. The generic Laws interface is discharged by `CanonicalPrimitives5.caller`; it adds no endpoint assumption. Challenge-side semantic/update/read composition and shipped/reference equality remain open. Producer list: `op121-producers.md`.

D234 retained: resume4's noncanonical Horner disagreement stays unchanged in its report, receipt and counterexample files. It does not refute the complete-Result arbitrary-input extraction row. The row has not been restricted, and no shipped fix was made.

For **transfer and withdrawal**, complete execution-reached sets remain unresolved; universally excluded entries: **none proved**. `FixturePrefix5.entered_input` proves op226 is first after entering either input's attempt; it does not prove retry/admission reaches that entry. Inventory **30 →30**, zero new shipped source laws and zero universal exclusions. Effect entries4,32,122,123,232,257 remain deferred with inherited exact reasons. cb4 op259 is PREPARED; rw21 op223 is reference-only. No duplicate credit.

Both fixture proof-byte equations, full audit/status equations, V163 and native nonvacuity remain exact/open. ProverRw21ModelInstance is published at f3071faf74 as a stable mathematical serializer; its deployed-input-to-Transcript construction is explicitly open. The earlier absence report was mistaken and is superseded by published-model-review.json. No endpoint premise was removed, weakened, added or changed: before/after endpoint statements and deployment conditions are identical. E1/E2, real RunJoin, L1/L2/L3, proof-account client and release dependency closure remain.

## Validation and stop

Lean **95/95**, IDs **38000–38094**, unique; 68 green/27 failed. Last3 reserved for final audit. Kani **6/6**:4 arithmetic gates pass,2 equivalence timeouts. No local Lean. Failure receipts and four dependency-order queue failures38079–38082 are retained. Later retries changed dependency fingerprints; no unchanged replay bypass.

| Target | ID | Exit | Wall | Peak RSS KiB | Swap | Revision | Axiom reports |
|---|---:|---:|---|---:|---:|---|---:|
| PV_Join_FinalAudit5A | 38092 | 0 | 0:03.37 | 4362788 | 0 | 753ed2cb7b | 118 |
| PV_Join_FinalAudit5B | 38093 | 0 | 0:03.44 | 4357684 | 0 | 753ed2cb7b | 118 |
| PV_Join_CombinedAudit5 | 38094 | 0 | 0:01.85 | 4347712 | 0 | 753ed2cb7b | 237 |

All236 PV_Join theorem/function declarations plus headline pass with standard axioms only. This is a focused audit against retained objects, **not a clean release manifest replay**. `receipt-index.json` contains every host target, exit, wall, RSS, swap, source revision/hash, dependency fingerprint and full axioms reports. Timeout child aggregate peaks are unavailable; wrapper RSS is labeled and live lower-bound samples retained. All observed swaps0; native scopes and Lean scopes retain6G/8G/swap0 caps.

No crates/programs, keys, sibling worktrees, launcher or backend changed. No push/merge. New Cargo target cache removed after completion; pinned Lean cache retained.

Stopped on budget exhaustion. Next: prove the canonical-domain source/reference sum3/evaluator correspondence symbolically, compose the challenge invariant into the actual op121 call, and compose the published rw21 serializer once its independently specified deployed-input-to-Transcript construction is proved.

Commits before this final evidence commit: `commits.txt`.
