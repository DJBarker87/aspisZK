# XRl obligation ledger

**Target not yet established. Actual-top premises removed: zero.**
Adopted top: `AspisR1.ARX_Root.deployed`. Full before/after statement snapshots
are byte-identical to `lean/ARX_Root.lean`. Recount: atomic quantified families,
SAME witness, shared families once, L185=L159 alias. Removed/added/changed
0/0/0; delta T0/P0/G0/C0. No quantifier, carrier, failure event, conclusion,
security metric, game, trust item or artifact change. Frozen3 and
RuntimePersistence retained. Local results below are not actual-top discharge.

| Row | Proved this round | Open / obstruction |
|---|---|---|
| Adapter equivalences | XRl_Adapter full local state laws for enumerateNext, intoIter, fromFnState, revRestored, enumerateRestored, closure_1 FnMut; explicit FnOnce and dropped-callback projection laws. | Universal reverseNext/next_back equality is FALSE: reachable exhausted singleton counterexample. Dropped next restoration cannot preserve arbitrary mutable-borrow writes. FnOnce final capture is not in fixed trait ABI. XRl_ADAPTERS.md is authoritative. |
| Restricted reverse caller domain | Full modeled reverse Result and state equality at cursor zero; fresh iter_mut supplies zero. next_back and restoration preserve cursor when used on the matching cursor domain. | Caller-wide transport/native P6 must be proved; this does not replace the rejected every-input request. |
| QueryGeometryLineInvariant | Full XRk named Prop: SAME accepted emitted for_range derives start, inverse cardinality, line_z cardinality. Actual mapped collector and loop invariants, no second success witness. | This named Prop contains ONLY cardinalities/start. Stronger native field-value/inversion, allocator/error/effect/source-to-ELF laws remain OPEN. |
| Line-value projection | One actual successful source iteration appends p.x,p.y,line_x,line_y,line_z in that order, and records SAME source square/double/one/sub calls for line_z. | Point/index-to-field mathematical interpretation, all-history source/native association and inverse field law remain OPEN. |
| DotCountProjection / histories | Actual accepted modeled pushes, initial new, chronological histories: count equals length ≤4096; scalars canonical; SAME operand sequence factors both dots and all four wrapping cell folds. | Native wide-operand producer invariant cannot follow from arbitrary extracted-carrier history: an accepted one-step history with noncanonical wide coordinate is proved. No claim of a native Rust bug. Wide validating constructors' canonicality is proved separately. |
| PreparedScratchProjection / PreparedClaimPowersAssociation | Imported XRk results unchanged; all-outcome scratch, reference powers and weighted parts not re-proved. | All native twelve-leaf P6, actual source invocation/effect/carrier association and actual-top installation remain OPEN. |
| CandidateTx1AcceptedPath | Imported XRk_Tx1Projection and XRk_Tx1Association unchanged. | Native compact/public parsing, authentication, expansion, chronological attempts/effects and carrier/source association remain OPEN. |
| AcceptedCandidateCheckpoint | Imported SAME-Prepared/checkpoint call projection unchanged. | Full saved-state physical-byte/native heap/ownership/ordered three-digest correspondence remains OPEN. Whole-checkpoint Kani shape timed out; split leaf checks do not establish it. |
| Native leaf checks | Optimized Kani: sparse coordinate0/1 single push; zero-addend frames; query-word serialization/frame; arbitrary canonical four/eight-limb byte serialization and roundtrip; truncated next header; all three variant layout sizes. | These exact domains are not generic field multiplication/history or whole prepared_claim/checkpoint P6. K005 timeout retained, no unchanged retry. |
| Actual top / release | Before/after unchanged; no premise discharge. | No joint SAME-witness inhabitant of all actual-top premises, full closure replay, source-to-ELF result or formatter reachability result. |

Non-vacuity is local: initial emitted dot history; validated wide zero domain;
noncanonical-wide accepted extracted history (a boundary counterexample); old
actual empty geometry-loop success reused. Empty geometry is not the ten-query
TX1 domain. Kani covers reach nonzero canonical words, maximal raw query word,
next>255 and all variants. No whole-top satisfiability claim.

A coherence finding is retained at L063: importing Port4C_GeometryStd beside
XRk_Types fails on duplicate global instDiscriminantCirclePointErrorIsize from
AspisR72Sampler.Types. The old module is not edited/substituted; local XRl_
scalar-clone/extend lemmas use the pinned standard library directly instead.

All accepted new theorems have standard-only #print axioms; failed diagnostic
sorryAx results are excluded. Per-attempt receipt/source snapshots distinguish
accepted proofs, errors, timeouts and the L081 own dependency-order refusal.
No shipped file/harness or wallet key changed; ELF rebuild trigger did not fire.

Final additions: XRl_CanonicalConstructors proves canonical new/from_qm31
outputs; XRl_WideCanonical proves from_limbs canonicality. XRl_InversionBoundary
proves only zero rejection and the successful exponentiation characterization,
not the field inverse identity. XRl_CheckpointBytes proves modeled encoding
sizes; XRl_CheckpointFinalizer proves the isolated final byte-size guard.
Whole checkpoint-model size projection L097 timed out at heartbeat200000;
its TX1 consumer is unaccepted. No native/top credit for either candidate.

Final budget:100 allocations (99 compiler invocations:78PASS/21FAIL; one own
missing-predecessor refusal charged),10 Kani (9PASS/1TIMEOUT),0 extraction.
No prover invocation is permitted after L100. XRl_Verification.json records
zero source/dependency consistency errors. L099 audits65 local theorems;
L100 audits103 externals plus6 emitted entry points, standard-only. This is a
focused coherent local-model cohort, not a security-top/full release replay.
