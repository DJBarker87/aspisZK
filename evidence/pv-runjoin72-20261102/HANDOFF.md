# Runjoin72 — D552 final handoff

Same worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry a778c445977bf568dda0cd81b7a63fe5b401909b.
Sole writer. No merge/push. Final source/audit revision is
06949c02fad7cbe6ebbbbcb4550ef88a5d86f8d9; reporting commits follow.

## Stop/accounting

**97/97 charged attempts spent:58 accepted,39 rejected. Budget zero.**
79600–79693 and79697–79699 charged;79694–79696 unused. All three final audits
passed. No pending shell, scope or reservation remains. Six host refusals were
uncharged, with180s cooldowns. Do not launch more compilers under this budget.
Reconciliation and original logs have been collected; REPORT-D552.md,
SUMMARY.json, SESSION-D552.json and target-results-D552.json are final.
The earlier running checkpoint is superseded.

## Checked proof frontier

NativeMultilinear72(79600), PointsTotal72(79605), NativePointClaims72(79606),
LiftRows72(79609), ProducedRows72(79611), ProducedClaims72(79613) establish
actual reached column shapes and point_claims success. SemanticSuff72(79614)
and SemanticPlan72(79631) use reached op227 terminal sufficiency.
BackendBuildBalanced72(79621), BuiltHelper72(79623), CaptureBuilt72(79627),
NativeCaptureBuilt72(79646) close the exact helper-balance post-build capture
tail, conditional on original successful build_with_material.
RoundSequencePlan72(79634), SumcheckPlan72(79647) bind all dependent source
rounds. AllocatorCompat72(79636) only equates statuses from BOTH fixed-world
and threaded-world success; it does not discharge either success.

NativeAssignment72(79641), NativeWorkerMerge72(79642),
NativeInterpolation72(79656), NativePolynomialBytes72(79657),
NativeRoundPolynomial72(79660), NativeSemanticRound72(79661) compose actual
op257 vector/count/callback agreement with reached op227 sufficiency, merge,
symbolic interpolation and exact896-byte source polynomial encoding.
PolyChannelsTotal72(79664), PolyBlockTotal72(79666), PolyEvalTotal72(79667),
NativeSumcheckArithmetic72(79668) close the actual evaluator totality/op121.
NativeRoundContinuation72(79669) composes storage/append/evaluation given
exact boundary, record, sample and room conditions. SumcheckFinish72(79649)
still requires actual terminal value equality.

WideLimbsParse72(79674), ByteWord72(79681), ByteArrayFour72(79683),
ByteWordGroups72(79684), PolyCellCanonical72(79691), PolyPayloadWindow72(79693)
are checked. The full32-byte parser assembly failed79685–79689; the source
was moved to drafts/ with the never-compiled NativeWideParse72,
NativePolyCellParse72, PolyPayloadCanonicalWindow72 and
NativePolynomialByteDomain72 adapters. NO credit for those drafts.

## Next work with a new authorized budget

1. Factor the source parser into opaque four-byte readers BEFORE expanding
   the entire32-byte term. Prove each reader using ByteWordGroups72, compose
   the8 reader equations and WideLimbsParse72. Do not repeat the expanded
   full-parser rewrites/whnf timeout or increase heartbeat/memory limits.
2. Independently check the draft canonical payload-window bridge; then use
   the exact896-byte source encoding to discharge record/header/field parse
   checks. Prove row order, hash/semantic transcript outputs and append room.
3. Derive each round boundary equation and final oracle-running equality from
   actual worker outputs. Produce the actual op257 vectors/count/agreement,
   both commitment workers' output/lane shapes, and each source/post-world
   allocator success/compatibility. Preserve the original callbacks/worlds.
4. Discharge NativeControl55.run's earlier audit/build prefix and compose full
   capture. Prove Nonempty P at opsNative. Only then remove NodeAppend with
   actual before/after evidence. Do not replace these by a consumer premise.

## Unchanged open status and qualifications

Nonempty P UNPROVED; NodeAppend NOT removed. Seven links before/after:
R24Sampler, CommonSample, BackendInput, QueryContext, QueryRange, NodeAppend,
PublishOrder. Earlier QueryAppend/FinishContext removals retained. No new
native consumer premise or ledger row removed; three TrustItems, observer,
simulator and release pins unchanged. Skeleton consistency remains reduced
to non-emptiness. Privacy target not yet established.

V183 Kani-backed support remains **SUSPENDED(K-3), D549**. Allocator family
retained in opsNative. V183-K3-D549.json pins research revision
21d447956e44895bbd1c235b5c16ae0c5aba8159 and full D549 excerpt. No restored
deployed credit; V370/compiler/extraction/source-binding qualifications stay.

Pinned runjoin32 cache reused; final preflight4223 projects/9482 fingerprints/
5673 external objects/5438 IR,9896 namespace checks, all match. Final audits
79697–79699 expose only propext/Classical.choice/Quot.sound. One module per
6G/8G/swap0/TasksMax64 scope, Lean-M7000; no limits increased.79601's memory
failure was replaced by generic mapped_total and narrower imports79602.
Full original module logs are losslessly collected with hashes. No frozen
manifest replay while capture is open. No Rust/Kani/SBF/ELF/key/funds work.
