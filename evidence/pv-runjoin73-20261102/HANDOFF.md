# Runjoin73 — LOG D558 context checkpoint

Same worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `0f4f8f5569`. Sole writer, no merge/push.
This is a CONTEXT CHECKPOINT, not budget exhaustion or task completion.

## Accounting and safe resume

58/97 charged attempts spent: **37 accepted,21 rejected**. IDs79800–79857
are consumed. **39 attempts remain**; normal IDs79858–79896 are unused.
Final audits79897–79899 are UNUSED and count within the remaining39.
The checkpoint integration audit79857 passed; it is not the frozen manifest.
No live own scope, reservation or transport remains. One uncharged refusal
at79851 observed the full180s cooldown and retried the SAME ID successfully.
Do not repeat accepted unchanged compiles or reuse a consumed ID.

Use `tools/pv-runjoin73-20261102/focused.py <ID> <module>`; sources must be
committed before staging. Same pinned runjoin32 workspace, one6G/8G/swap0/
TasksMax64 scope at a time, Lean-M7000, default heartbeats/recursion. Limits
were never raised. The own wrappers carry the earlier failed-source guard
and accepted-prerequisite guard, with prior72 plus current73 receipts.

## Checked frontier

All new sources live under `docs/research/v8-r0-zk-20261009/lean/R1Z/`.
Their exact accepted revisions, hashes, axioms, wall/RSS/swap are in
`target-results-D558.json`; full original logs are losslessly collected.

1. **Full wire parser solved.** FourReader73(79800) is an opaque four-byte
reader preserving source read/error order. WireReaders73(79801) proves its
8 concrete-position laws using ByteWordGroups72. FactoredParser73(79803)
factors the source on ABSTRACT slices. WideWireParse73(79804) composes the
8 opaque reader equations with WideLimbsParse72. No expanded concrete
full-parser rewrite and no heartbeat increase. NativeWideParse73(79806)
binds the actual native op50/c1 entries.
2. **Draft bridge independently checked and consumed.**
PolyPayloadCanonicalWindow73(79805) fixes the missing ExternalTypes binder
and proves each payload window canonical with zero high limbs.
NativePolyCellParse73(79809), NativeCanonicalParse73(79815),
NativePolynomialWindows73(79817), NativePolynomialValidation73(79818),
NativePolynomialByteDomain73(79819) connect the original896-byte encoder,
actual source range reads, full canonical parser and high-limb rejection
check through all28 validation-loop cells. FieldValidation73(79813) is a
symbolic bounded source-loop proof; PolyOffsets73(79814) proves wrap/division
bounds. No full-capture or parser-success premise was installed in a consumer.
3. **Record and transcript tail solved locally.** FrameViews73(79822),
RecordParser73(79824), NativeRecordParse73(79825),
NativePolynomialRecord73(79827) construct the exact5-byte header and896-byte
payload, prove source record AND parse success, and prove length901.
NativeRoundShape73(79828), RoundRow73(79835) establish exact row shapes and
symbolic counters. NativeSamplerTotal73(79831) is total on arbitrary original
blocks. NativeSemanticSample73(79833) preserves the ORIGINAL hash callback,
its three ordered requests, row advance and hash state. It still needs
original hash totality and row order, not a changed hash or zero stub.
NativeRoundTail73(79836) discharges encoding, record/parse, sampling, point
storage, evaluation and append room. Remaining hypotheses are boundary
Result equality, actual row order, original hash totality and actual output
length171+901*round. Length171 is an explicit invariant here, NOT yet proved
for the earlier source prefix. The conclusion advances it by exactly901.
4. **Boundary values now connected, not only total.** BoundaryWords73(79837)
and BoundaryFold73(79838) prove integer accumulation/no overflow symbolically.
BoundarySource73(79843) factors the actual flat source through opaque initial
and advance operations. BoundaryReduceValue73(79846), BoundaryFinish73(79847),
BoundaryPolynomial73(79848), NativeBoundaryValue73(79849) prove the actual
native boundary Result is canonical and has value p(0)+p(1).
NativeInterpolationValue73(79845) retains the full interpolation sample law
at every Fin28 node. CanonicalInjective73(79850) turns canonical value equality
into raw equality. NativeInterpolationBoundary73(79851) derives exact boundary
Result equality from a canonical running claim with value equal to the first
two ACTUAL merged values. The running-sum invariant remains unproved globally.
5. SliceImage73(79853), NativeMergeValue73(79854), InterpolationCells73(79855)
preserve actual slice images and ordered worker sums through native merging.
**NativeWorkerRound73(79856)** composes the WHOLE original source round,
including its actual original worker callback, merge, interpolation, boundary,
record, semantic sampling, point update and append. It preserves original
worlds/callbacks. Its still-explicit local hypotheses are: actual op257 map
success, exact returned length and per-index successful values; canonicality
of those values and running claim; the mathematical running-sum identity;
original transcript hash totality, row order and output-length invariant.
It does NOT prove production of the worker packet or discharge those
invariants globally. No new endpoint consumer premise was added.

## Next work, in order

- Derive actual op257 vectors/count/per-index callback agreement and canonical
value laws; use NativeMergeValue73 and NativeWorkerRound73. Do not replace the
actual worker by a reference dictionary or assume its selected source law.
The installed native dictionary preserves original op257; V263 remains open
in the existing ledger. Existing WorkerObstruction63 shows why unrelated
existential worker success is insufficient; it is NOT a deployed counterexample.
- Prove the running-sum invariant and native op121 value/canonicality law,
then transport the last-round value to the original oracle. The new boundary
and interpolation value laws are ready. Preserve all source assignments.
- Prove the earlier transcript prefix's actual row15/output171/hash invariants;
produce both commitment-worker outputs/lane shapes and the original fixed-world
AND threaded-world allocator successes. AllocatorCompat72 proves neither.
- Discharge NativeControl55.run's audit/build prefix, compose full capture and
prove Nonempty P. Only then remove NodeAppend with actual before/after evidence.

## Terminal dependency — do not invent its missing equality

Read `op227-dependency.json` and the read-only upstream snapshots
`op227-D557-HANDOFF.md` / `op227-D557-EXACT-BRIDGE-STATEMENT-D557.json`.
Upstream branch `codex/pv-b3p6-20261028` at784bf3c44b485b48e94d4319b624a8054e0381fb
STILL reports the unconditional deployed bridge OPEN. The exact named consumer
is `R1Z.PV_RunJoin_OracleBridge38.selected_callback`. Upstream
`PV_B3P_Closure557227.selected_callback_residual557` still depends on the OPEN
`PV_B3P_Closure557227.DeployedWrapper557`; never assume or install that wrapper.
No upstream code was merged, restated as an axiom, or assumed in this work.
The requested conditional Nonempty theorem is not yet proved: the other
capture obligations above are also open. Once those close, condition the
endpoint on EXACTLY the named selected_callback bridge statement if upstream
has not landed. SumcheckFinish72 still needs the actual terminal VALUE equality;
terminal existence/totality is insufficient.

## Unchanged endpoint and qualifications

**Full capture/Nonempty P UNPROVED; NodeAppend NOT removed.** Seven links
before/after: R24Sampler, CommonSample, BackendInput, QueryContext, QueryRange,
NodeAppend, PublishOrder. Earlier QueryAppend/FinishContext removals retained.
Zero new native consumer premises and zero ledger rows removed. Three TrustItems,
observer, simulator and release pins unchanged. Skeleton consistency remains
reduced to non-emptiness. Privacy target not yet established.

**V183 Kani-backed support remains SUSPENDED(K-3), LOG D549.** The allocator
family remains installed. V183-K3-D549.json retains research revision
21d447956e44895bbd1c235b5c16ae0c5aba8159 and the complete cited excerpt.
No restored deployed credit; V370/compiler/extraction/source-binding
qualifications remain. No Rust/Kani/SBF/ELF/key/funds work.

## Validation/recovery notes

CheckpointAudit73(79857) imports all36 accepted normal modules and checks83
named declarations; only propext/Classical.choice/Quot.sound. Source audit
checks37 accepted current source hashes (including audit). All21 rejected
attempts/logs are retained, and no failed proof source was retried unchanged.
BoundarySource73's79839 default-heartbeat failure was fixed by sealing the
initializer, then normalizing only small source index values before composing
opaque updates;79843 passes in2.27s. No limits raised. The initial local
BoundaryFold staging refusal was uncharged: two out-of-plan imports were
replaced by small new generic BoundaryWords73 over an already pinned import.

Receipt wall118.45s, peak4,587,028,480 bytes, swaps0. Reconciliation matches58
host results and174 shared evidence files; no other-job ID hits or live own
scopes. Fresh preflight4260 projects/9595 fingerprints/5673 external objects/
5438 IR companions: all match. Namespace resolution9933 checks, zero links, all match. No frozen manifest replay while capture is open.
The final source checkpoint audit revision is recorded in SESSION-D558.json;
reporting commits follow. Keep the caches and every source/evidence input.
