# Runjoin72 LOG D552 — running checkpoint

Same worktree /Users/dominic/ZK/.worktrees/pv-runjoin, branch
codex/pv-runjoin-20261026, entry a778c445977bf568dda0cd81b7a63fe5b401909b.
Sole writer. No merge/push, implementation, keys/funds, Rust/SBF or Kani work.

## Accounting at this checkpoint

63/97 charged attempts; 41 accepted, 22 rejected; 34 remain.
IDs79600–79662 are charged. Never reuse a compiler ID. Audits79697–79699
remain UNUSED. The focused wrapper is currently retrying UNLAUNCHED79663
PolyChannelsTotal72 after a cgroup-scan race refusal and full180s cooldown.
The same shell schedules79664 PolyBlockTotal72,79665 PolyEvalTotal72,
79666 NativeSumcheckArithmetic72,79667 NativeRoundContinuation72 ONLY if
predecessors pass. Reconcile that shell and receipts BEFORE another launch.
No refusal is charged. See all receipt-/modules-/refusal-*.json files.

## Checked endpoints

NativeMultilinear72(79600), PointsTotal72(79605), NativePointClaims72(79606)
close native statement points and all29 source column evaluations for rows1024.
LiftRows72(79609), ProducedRows72(79611), ProducedClaims72(79613) derive the
row shapes and point claims from the actual reached lifted columns, with no
new consumer premise. SemanticSuff72(79614) and SemanticPlan72(79631) consume
op227 success on the exact SOURCE-produced claims. The original callback and
all local error branches are retained; no callback source credit restored.

NativeCaptureBuilt72(79646), via BackendBuildBalanced72(79621),
MaterialBackendBalanced72(79622), BuiltHelper72(79623), CaptureTail72(79625)
and CaptureBuilt72(79627), proves the final native capture tail after an actual
successful build_with_material. The source helper-balance guard is retained
through the exact padded helper and lifted column26. There is NO assumed
capture-success input. Earlier audit prefix and build success remain open.

RoundSequencePlan72(79634) and SumcheckPlan72(79647) reify the complete ten
source rounds, original worker outputs and dependent point/running/transcript/
byte continuations. Final oracle comparison is retained. SumcheckFinish72
(79649) closes it at the exact expected oracle value, not from totality alone.
AllocatorCompat72(79636) proves compatibility from success at BOTH fixed and
threaded worlds; it does not assert adequacy or world equality.

NativeAssignment72(79641), NativeWorkerMerge72(79642), NativeInterpolation72
(79656), NativePolynomialBytes72(79657), NativeRoundPolynomial72(79660), and
NativeSemanticRound72(79661) compose the actual op257 output/count/per-index
callback agreement and reached op227 condition through the complete merge,
interpolator and896-byte polynomial serializer to the exact remaining source
round continuation. The interpolation fixed point was transported by equality
of its functionals and proof irrelevance; NO28x28 concrete recurrence reduced.

## Pending and next work

Current UNCHECKED drafts: PolyChannelsTotal72 has a changed source after79662
(parse error plus whnf timeout); now named opaque primitive bind laws replace
the rejected unification shape. Then prove polynomial block/loop totality and
native op121, which NativeRoundContinuation72 consumes. ByteInspect72 is an
UNCOMPILED diagnostic for future exact record/header/field validation.

After those: discharge each source record and transcript success on serialized
polynomial bytes, including row order, hash result, parse fields and append
room; prove each round boundary equation from actual workers, not just worker
success. Compose ten rounds plus actual terminal value comparison. Prove both
commitment worker outputs/lanes, each allocator source/post-world success and
compatibility. Discharge NativeControl55.run's earlier audit prefix, build the
full run/capture, hence Nonempty P at opsNative. Then NodeAppend with before/
after; then remaining links. Do not replace any of these by a consumer premise.

Nonempty P UNPROVED; NodeAppend NOT removed. Same seven links before/after:
R24Sampler, CommonSample, BackendInput, QueryContext, QueryRange, NodeAppend,
PublishOrder. Prior accepted QueryAppend and FinishContext removals retained.
No ledger row or new privacy premise removed; three TrustItems, observer,
simulator and release pins unchanged. Skeleton consistency: reduced to
non-emptiness. Privacy target not yet established.

## Qualifications and verification

V183 Kani-backed support remains SUSPENDED(K-3), D549; installed world-indexed
allocator family retained. V183-K3-D549.json pins research21d447956e44895b...
and the D549 excerpt. These Lean proofs do not restore deployed support.
All V370 and existing extraction/source-binding qualifications remain.

Pinned runjoin32 cache reused. Fresh initial preflight:4165 project objects,
9324 direct fingerprints,5673 external objects,5438 IR companions;9838 namespace
resolutions,all match. Original compiler logs are on host under per-module
output_path and must be collected losslessly before final reporting. All
accepted targets print standard-only axioms; final audits not yet run. Caps
remain6G/8G/swap0/TasksMax64,Lean-M7000.79601's memory failure was replaced by
generic mapped_total with narrower imports; it passed79602. No limit raised,
no unchanged failed source rerun, no full manifest replay while capture open.
