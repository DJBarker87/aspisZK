# L166 proof4 handoff — target not yet established

Branch: `codex/cx-l166-proof4-20261027` (the checkout's existing branch; the
prompt's 20261026 spelling was not used to switch or edit another worktree).
Base: eb7eab86b9e06595ce4e37a7f20fe44616d845e1. All stage commits are local;
no push, merge, session A worktree/candidate edit, wallet or key operation.

## Result and exact limits

The owned reference recorder, stateful reference-model BothSlots theorem,
reached-input/original-cylinder consumers, queried-address prefix export, and
conditional original-account composition compile. **L166 is NOT removed.**
Whole instrumented shipped batch Result AND chronological log equality is not
yet certified. Passing local Kani gates and a Lean controller induction are
not promoted to a complete physical-runtime refinement.

`lean/BEl_NativeBatchCut.lean#observation` proves
`BEh_Scope.BothSlots (fun _ _ _ => True) (native call hashv) (source call hashv)`.
Here native is the explicit reference interpreter with a pending-before-call
recorder, NOT the opaque D188 native function decorated with a source log.
`BEl_PhysicalCut.transfer` displays the missing physical/reference success/rejected-prefix association
premise; it is not discharged, added to actual-root binders, or counted away.
The exact statements are in BEl_MODEL_BOTHSLOTS_kernel.txt and
BEl_PHYSICAL_BRIDGE_kernel.txt. No physical closure credit is taken.

`BEl_Top.deployed` has EXACTLY Rc10's original binders. It retains Rc10's entire
conclusion and adds `BEl_Packet.Facts` for the computed reference observer.
This output strengthening is explicitly NOT the requested deployment theorem
with L166 removed modulo only ARQ. BEl_BEFORE/AFTER_statement.lean.txt contain
the source statements; BEl_BEFORE/AFTER_kernel.txt contain fresh complete
pretty-printed types without ellipses. BEl_check.py compares literal binders
and the retained conclusion. Rc10 source SHA remains
c5c85966b83fbaf24626724fe9becdef92214389fb4286d6ba0d304f486e1527.

## Composition in dependency order

1. BEl_Recorder, FullLog, CoordinateLog and SourceRecords establish exact
   occurrence/parts/byte/reply reconstruction, including repeated addresses.
   PartialRecorder includes backend nonreturn; PrefixRecorder and LocalCut
   append a fresh local recorder at a pre-existing chronological cut.
2. LeafReference range-order equivalence -> CodeCongr bind congruence ->
   BatchStep -> BatchLoop -> BatchTree -> Batch -> ReferenceSource.
   The original P6 count/padding/verify denotation and Port4B scratch induction
   are reused; no repeated array induction or helper stubs are introduced.
3. NativeBatchCut.observation/logs -> SlotObservation current/stage prefixes ->
   ReachedReference.cuts uses BEk's SAME native reached operand tuples ->
   OriginalReference.selected uses ARU's original partial-account cylinder.
   The queried-address prefix is exported for the reference observer. Its use
   as a PHYSICAL recorder prefix still requires the missing source certificate.
4. AccountComposition.conditional uses literally `ARQ_Join.Target`, followed by
   RPx_Transport.transport and RPx_AccountCharge.charged on the same installed
   configuration, adversary, account, observer and selection. The source-prover
   and original-account recorders are not equated. No replacement failure
   event, global P1 at ideal H, universal support or new runtime trust is added.

ARQ's exact same-experiment event/recorder join remains the L159/L181 deliverable
(L185 is L159's alias). ARU's universal-range and independent-runtime limits
remain inherited. Neither ARQ nor those limits are the local recorder bridge.

## Recount and non-vacuity

BEl_ledger_rows.json retains the exact atomic predecessor ledger. The method
counts actual antecedents, then distinct deployment-only rows, counting L185
as L159 once; native and source-global finish rows remain separate. Before AND
after: actual **83T/12P/13G/0C**; deployment-inclusive **89T/16P/13G/0C**.
Delta: **0**. No row reclassified, packaged into a new trust item, or removed.
BEl_validation.json and BEl_RECOUNT.json record the independent enumeration.
The fresh root-type audit reuses the predecessor's unchanged expanded atomic
family inventory; it is not a new full frozen dependency replay.

No antecedent was strengthened or false premise introduced in BEl_Top.
BEl_Nonvacuity.rejected proves two repeated attempted calls and state updates
survive rejection. Optimized Rust fixtures compare FULL Result/log equality
on both ordinals: successes84/90 attempts and padding rejections10/12 attempts.
They use a constant backend and zero-valued local proof/root/queries. They are
local non-vacuity evidence, NOT real SHA, adversarial completeness, or a jointly
realized deployment/root hypothesis fixture. Joint release non-vacuity remains
unestablished; no imported conditional fixture is called an unconditional one.

## Validation, resources and frozen artifacts

**52/100 Lean attempts:40 passed,12 excluded development failures;20/20 Kani
proof runs:10 verified,10 excluded;1 CBMC loop inspection;3 optimized Rust
fixture runs:2 passed,1 initial include/doc-comment error;1 Charon invocation
failed before extraction.** K14 is the inspection, so K21 is the twentieth
proof run, not a twenty-first run. No further Kani run is authorized or hidden.
48 Lean attempts remain unused; this handoff does not claim the requested
whole-budget completion. The P6 model/reached/account work continued after the
Kani budget was used; its output does not close the remaining physical bridge.

Each attempt's receipt/source snapshot/stdout/time and BEl_attempts.jsonl record
exact target/command, revision and dirty-source hash, direct object fingerprints,
exit, wall, peak RSS, swaps and full axioms output. Successful new theorems use
only propext, Classical.choice, Quot.sound (or fewer). Failed elaborations with
sorryAx in diagnostic output are excluded, never treated as proofs. The final
focused union/type/axioms audit is BEl_052: exit0,2.341775757s,
RSS5548104KiB,swap0; no package or full frozen manifest replay occurred.

All host jobs used one own capped scope at a time after the existing reservation
barrier: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; Lean -M7000;
optimized Rust and Kani compilation. The largest reported RSS was6515292KiB
(K17, excluded); no cap was raised. Timeout replacements isolate or change the
problem, never rerun an unchanged killed/timed-out target. Strict Kani admission
requires VERIFICATION SUCCESSFUL exactly once and no VERIFICATION FAILED;
exit0/manual success after timeout is insufficient. BEl_KANI_RUNS.md inventories
every gate, exclusion, bound and replacement, preserving failed attempts.

BEl_CORRESPONDENCE.md records every owned Rust body line, concrete source cut,
direct Lean model and exact gate scope. BEl_source_cuts.json pins original
bodies/constants; BEl_lean_cuts.json pins the parameterized native step copy.
BEl_generate.py --check passes. K21's Rust core token sequence is unchanged
by moving owned code into an include file (whitespace/comments aside). The
later extraction-only cfg is disabled for Kani and tests; it adds no shipped
code. No candidate installation, Cargo lock, shipped crate, release feature,
wire format, parameter, metric, security game or admitted trust item changed.
Frozen3, RuntimePersistence and the owner-approved game clauses are retained.

No SBF rebuild ran. The cfg(kani) module was added ONLY in the standalone
EVIDENCE crate, which declares its own workspace and is absent from all shipped
workspace members/dependencies. No cfg(kani) module was added to a shipped
crate. The three ELF pins are inherited, NOT freshly rebuilt/confirmed here:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

The coherent SInt2 workspace and pinned candidate objects were reused. No
unchanged dependency rebuild was needed. Final own scope inspection covers
77 invocations, all gone/unpopulated. The known own BEl_target cargo cache
(76708KiB) was removed. No surviving /tmp solver file overlaps any own Kani
run interval; unattributed foreign files were untouched. New Lean cache objects
remain in the coherent workspace for lead reuse, with source/size/hash pins;
no objects, binaries, archives, ELFs or keys are committed. Source diff checks
pass; raw compiler diagnostics are retained byte-for-byte, including emitted
trailing whitespace. BEl_check.py audits sources, receipts, limits, budgets,
source identity, standard axioms, exact binders, conclusions and row recount.

## Exact obstruction and next deliverable

The new recorders are real safe Rust, not a fabricated Lean history, and the
source model/reached operand association is useful progress. What is absent is
a complete certificate transporting their physical observations on the shipped
call tree to that reference on every admitted reached input. The existing
D188 extraction still returns values only. Existing library/runtime admissions
cannot be silently extended with an independent recorder field. The local
reference packet does not substitute for ARQ's event/recorder join; the account
theorem remains conditional on ARQ literally, rather than consuming that packet
as a proof of the missing global target.

The passing Kani gates cover leaf bytes/results, one scratch step for all trees,
8-byte padding predicate, one actual Vec recorder entry/projection, and the
same-allocation opening geometry. The whole attempted chronology across the
leaf-loop/count/padding/verify/triple context has no complete Rust certificate.
The inherited P6 parent/helper facts and symbolic controller induction are
retained as predecessor evidence, not mistaken for that enclosing concrete
physical instance. `BEl_LawComposition.trans` preserves exactly BEh's permitted
rejected-error/rejected-state freedom. The future transfer premise is the
success/rejected-prefix association, not an unnecessarily stronger equality of
Rust error constructors with source panic markers.

A direct extraction attempt was also prepared for BOTH generic explicit-log
entry points (`BEl_rust/src/BEl_extract.rs`, disabled cfg in all other builds).
BEl_C01 exits127 before compiling/extracting anything:

```
timeout: failed to run command '/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon': No such file or directory
```

This is a missing pinned compiler, not an Aeneas semantic counterexample.
No generated extraction, Aeneas run, extra trust or verified Rust body follows.
local-lean.txt rule5 says: "Do NOT build or repair build/launcher/monitoring
infrastructure. If the launcher or host misbehaves, stop and report the exact
error in one paragraph; the lead fixes infrastructure." No toolchain/launcher
repair, replacement compiler search or cap increase was attempted. Independent
BEh-law composition was checked afterward; the extraction item remains stopped.

Next: restore the pinned compiler through the lead's infrastructure path, then
extract/relate the explicit recorder (or finish the scoped P6 body certificate
from the saved exact loop cuts) and instantiate `BEl_PhysicalCut.transfer.bridge`
on the SAME BEk reached operands, ordinal, borrow/allocation geometry and
backend state. Parent/helper calls must retain chronological recording; do not
infer it from equal Results. Then the existing reference prefix and source
accounting consumers are ready for ARQ. No further Kani invocation fits this
job's20-run budget;48 Lean attempts remain. No additional authorization for
Kani or change to the security contract is presumed.
