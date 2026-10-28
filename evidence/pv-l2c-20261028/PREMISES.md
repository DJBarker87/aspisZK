# D370 current disposition — checked N3 counterexample

Target not yet established. Successful canonical preparation can retain raw
M31(P) at C1[0][444]; native masking preserves it and N3 rejects it, whereas
the same-public M31(0) case passes the exact-body guard diagnostic. The actual
secure prover entry with OS entropy returns Err(Semantic) on the bad case.
Work stopped under the explicit counterexample rule, with 97 Lean attempts
unspent and no new Kani. V352/V354/V357/V360 remain OPEN/P; zero premises
removed, added, weakened or changed. Frozen implementation and HonestInput
are unchanged. Current evidence and accounting:
[resumed finding](resume-d369/D370-FINDING.md),
[state reconciliation](resume-d369/RECOVERY-D370.json),
[native receipt](resume-d369/canonical-n3-probe5/receipt.json).

The earlier dispositions below are historical and superseded by this finding.

---

# Before / after accounting

The before state is the candidate e461dca06a plus the authorized runjoin merge;
rows are from research:evidence/privacy-recount-20261026/ROWS6.md (recount 6),
with LOG D272/D276/D283 and candidate pv-l2b evidence. No global ledger edits.
The requested carrier is exactly R1Z.PV_RunJoin_ConsumerBoundary25.HonestInput,
with the honest prover's randomness, not a guard-success predicate.

| Row | Before | After this work | Residual preventing subtraction |
|---|---|---|---|
| V352 | OPEN/P, bucket b | OPEN/P, unchanged | E1/E2 actual stream/source/environment association, witness-independent failure/public signal and complete observation coupling; local sampler range laws do not supply these |
| V354 | OPEN/P, bucket b | OPEN/P, unchanged | Same-attempt stream/retry/failed-prefix association and real RunJoin coupling; neither arbitrary canonical randomness nor an ideal simulator is a native entropy law |
| V357 | OPEN/P, bucket b | OPEN/P, unchanged | Honest compiler/native canonicality and padding caller transport; helper multiset and inverse boundary; native oracle/interpolation/running-claim provenance |
| V360 | OPEN/P, bucket b | OPEN/P, unchanged | Public inactive geometry / packed masks / compiler D association, full balancing caller association, P_R1 factoring/certificate and timer/panic/retry observations |

Removed: zero endpoint or deployment premises, zero rows. Added, weakened or
changed: zero premises. T remains EXACTLY entropy_law, entropy_kernel,
observation. V371 physical timing remains substantive; DOITM stays disabled.
N5 poles may only use the existing same-attempt poleBad = P ∧ ¬V accounting;
no generic parser/helper/sumcheck error has been renamed a charged bad event.
No new exceptional event is claimed in this work.

The local universal raw-word and extracted primitive laws quantify over all
canonical values, so their arithmetic content is not fixture-specific. They
do not yet quantify over native executions generated from HonestInput.
The fixture honesty theorems provide non-vacuity of that carrier, not a
substitute for the missing caller association. The admitted but failed full
withdrawal from runjoin27 lies outside this carrier and is not a checked
honest guard counterexample. No honest guard counterexample was found.

N3 statement audit: UniversalBuild22.build_eq concludes equality after
PV_Src_NativeInput.columns / WriterRefine.liftU decode the words into the field.
It does not itself assert each native U32 is <P. Raw words P and 0 have the
same field image, so this decoded equality alone cannot discharge canonicality.
This is a diagnostic of a missing implication, NOT an honest-input guard
counterexample and NOT a reason to stop the requested counterexample search.
Checked's digest bounds and the native compiler's raw arithmetic/write range
invariant must be transported through the real returned bank/column pipeline.

## D355 final accounting (supersedes the historical audit status)

All four before/after rows above remain OPEN/P, bucket b. Universal
HonestInput compiler/returned-bank/decoded-trace identification is now proved
by HonestCaller; total/inactive decoded helper sums and pole-free decoded
validity are proved by HonestHelper/HonestValidity. These reduce local proof
work, without removing the native caller/materialization obligations.
The complete extracted balancing returns, parser composition and decoded
sumcheck boundaries pass the corrected combined audit and focused replay.

For V352/V354, E1/E2 streams, retries and failed prefixes remain. For V357,
the actual native table, raw compiler C1/D ranges, native helper/inverse and
oracle/interpolation provenance remain. For V360, the native public mask
geometry, every audited native column's origin, complete guard caller and
observation/certificate transport remain. No premise is relabelled as trust
or as a new charged failure event. Final receipts: 44897–44899; complete
fingerprints: resume-d355/final-closure-check.json. See REPORT.md for exact
result classes. No whole native per-site constancy theorem is claimed.
