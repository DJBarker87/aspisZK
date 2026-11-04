# D570 resume — active proof work

Exact worktree /Users/dominic/ZK/.worktrees/pv-rdcd3, branch codex/pv-rdcd5-20261101,
base a9aa230d1e9be0502b0e755540be7d22b2efd6ab. No push/merge/key changes.
User scope V197 only; 60 Lean, 10 native, 0 Kani. Lean90700–90796, audits90797–90799,
nativeN90800–N90809. New modules keep required PV_RDCD5_ prefix.

Read prior rdcd5 REPORT/HANDOFF and prompt rdcd6 -> rdcd5 -> rdcd4, current
pv-common/r1p-common/local-lean, root AGENTS security discipline, LOG D42–D68.
Those available prompt/rule inputs are committed under inputs/. The next link
prompt-pv-rdcd3.txt is MISSING from scratchpad and tracked files; an async
question to the lead asks to restore it. No answer yet. Continue independently.

## Inventory and immediate report

CONSUMERS.md, CONSUMERS-census.json, CONSUMER-variants.json retain source grep
for 107 refs/77 revisions (all local+remote branches, candidate included), full
reverse import cone and every source variant. 19 unique files, each identical
where present across refs. Code-file grep (*.lean,*.py,*.sh,*.rs); historical
receipt text is not executable use. Initial cancelled all-file scan extras are
also retained. Immediate commentary to lead: only V197 local short_failure and
credited diagnostic/replay are kind-sensitive; V197 was never restored. No
RESTORED row depends on wrong constructor. V236 uses bounded SUCCESS windows of
old shared helper, untouched by correction. All other branches read only.

## Correction and draft proofs

Owned PV_RDCD4_BytesSource changed ONLY import plus its three index calls:
now PV_RDCD5_ParserRange.index, with same predicate/window, failure .panic.
Old shared SliceRange194 stays unchanged (V236). ParserRange.binding proves
arbitrary-slice complete Result equality to the EXISTING Aeneas range index.
ParserWindows rdcd4/5 bounded component proofs use the new success lemma.
V197 rdcd4/5 references/short_failure now explicitly panic; rdcd4's uncompiled
bind_eq_iff draft also gets rdcd5's established congrArg proof repair.
Historical rdcd5 receipts remain untouched. ParserErrors now owned_empty=panic
and carrier_agreement (old mismatch removed, not repurposed). Old FinalAudit
queries agreement, FocusedReplay v197_finding explicitly becomes v197_corrected,
FrozenManifest queries corrected name. These full old unrelated suites are NOT
to be recompiled; scoped affected-consumer projection checks exact proof text.

New drafted ParserTransport (UNCOMPILED): scalar/convert/component/complex_shape/
complex/quartic exact arbitrary-slice equality; ParserFlat is imported.
New V197Restored (UNCOMPILED): parser_instance at original source callback,
window_instance, input_frame, rdcd4_instance. Existing op71_source law consumes
exactly this parser; importing its entire dictionary would pull 373–442 modules,
so no whole-dictionary/endpoint credit. Source callback boundary is the qualified
restoration target. No new input guard, eager16 check, error erasure or premise.

Source gate parser-source.py ran locally (inspection only), v197-source-bindings
records 3 application and 9 library bodies, exact before/after model, unchanged
1.94.1 deployed features/profile reuse. Structural argument, not native universal
or binary proof. Source-to-codegen V370/D381/D386 and physical observer retained.

## Actual launches / budget

- N90800 FAILED preflight: effective shared first Aeneas root lacked Global.
  Own staging-input failure, fixed source; no Lean compiler launched.
- N90801 PASS: private complete plain-copy overlay, all5673 h4 object hashes and
  companions verified. No project caches reused (rdcd4/5/pv-dlib caches cleaned).
- 90700 PASS unchanged required dependency PV_RDCD4_SliceRange194.
- 90701 FAIL ParserRange.binding: scalar-vs-Nat comparison syntactic mismatch.
- 90702 PASS changed ParserRange.binding (added UScalar.le_equiv). One uncharged
  pre-upload aggregate-reservation refusal; waited full cooldown, SAME ID retry.

Thus 3/60 Lean (2pass,1fail), 2/10 native (1pass,1fail), 0 Kani; next90703 andN90802.
All actual scopes 6G/8G/swap0/Tasks64, Lean-M7000, source/dep/ID receipts present.
Failed sorryAx diagnostic at90701 is rejected elaboration, not admitted source.
Never resubmit unchanged failed proof. No scope currently running except check
local session state: stage.py was launched in exec session6377 and may still
be uploading sources. Last driver to90702 completed. Scripts retain >=183s
between launch completions and next scope, plus >=180s after admission refusal.

## Tools and next steps

Own tools tools/pv-rdcd7-20261102/{scope,lean,drive}.py adapt existing rdcd5 tools;
no shared launcher/monitor modified. Source files MUST be committed before lean.py.
source-resolution.json updated by stage.py includes final full small closure.
stage.py uploads committed sources after fresh admission, records refusal history
under stage/; fetches preflight result. If refused, wait180s and retry (no scope).
Run `python3 tools/pv-rdcd7-20261102/drive.py 90703 R1Z.PV_RDCD5_ParserTransport`
after stage completes. It compiles prerequisites serially with cooldowns and stops
on any failure; edit/commit source, then next unused ID. Check driver through
semantics: it skips passed modules; if through target already passed, do not rerun.

prepare-audits.py generated V197ConsumerReplay (EXACT v197_corrected proof text,
namespace mapping only), V197Audit (46 full types + SUMMARY #print axioms),
V197Focused and V197FrozenManifest. consumer-audit-projection.json retains exact
snippet/hash and scope. All affected substantive source consumers need compilation;
audit-only wrappers use affected query projection, unrelated old suites not rerun.
NEPAudit copies research:evidence/axaudit2-20261102/NEP_WALKER.lean EXACT logic.
NEPDriver derives from fixed NEP_Driver, importAll/private/HARD unresolved errors;
roots extended to all46 queries, loads V197ConsumerReplay. Must run it as main at
reserved90797 (e.g. Lean --run with own env/cwd) after ordinary proof/statement
gates. #print summaries alone are insufficient under ax1/ax1'. No NDR/XR/Stream A
objects. Need preserved exact source hashes/provenance for walker copy.

Still required: compile all small corrected source/model/transport/consumer proofs;
fix genuine failures; statement audit; coherence check vs all launch fingerprints;
90797 combined raw+summary audit,90798 focused,90799 ONE frozen final replay;
final REPORT/ROWS/RUNS/association beforeafter, cleanup OWN object caches last.
No full manifest rerun unchanged. Keep T exactly entropy_law/entropy_kernel/
observation; endpoint premises unchanged. E1/E2, real RunJoin/world/physical
observer, client route and L1/L2/L3 remain. Privacy target not established.

## Latest checkpoint

Driver exec session19289 is ACTIVE, launched90703 through ParserTransport using
current25-module plan. 90703 TryArray194,90704 Endian194,90705 ExternalTypes,
90706 FullTypes,90707 FieldSource all PASS. Thus8/60 Lean used (7pass,1fail),
2/10 native (1pass,1fail),0Kani. Next90708 BytesSource; driver will stop on failure
or after ParserTransport (expected90714 if no further errors).
Transport scalar draft now explicitly unfolds the two P constants, because
FieldSource.P is irreducible. Uncompiled Restored adds native_window (actual
checked source window to cmAt); prepare-audits and NEP roots now47 queries.
These late source proof edits are committed but source-resolution/host stage
hashes need refresh before final coherence (lean.py transports each actual
committed target immediately before its compile, so focused launches are current).

Supplemental all-file textual reference scan ACTIVE in exec session97733, script
all-references.py. It scans9 distinct revisions whose complete executable-source
census contained the model; negative executable-source results cover remaining
refs. Output ALL-REFERENCES-census.json complete=false until finished. Prior
77-revision all-file scan was cancelled as unnecessary after1 negative revision;
no compiler involved. Code census and consumer variant census are complete.

BEFORE-sources.json preserves old model and counterexample proof verbatim with
revision/blob/hash. Native-validation-reuse.json pins historical6,420 paired
parser cases (panic.is_err then exact Option on success), FINITE validation only,
not a constructor-equivalence proof. No native rerun; all Rust unchanged.
NEP-provenance.json pins the exact fixed walker source and original driver.
coherence.py and audit-runtime.py drafted; final coherence must exclude
NEPDriver from object-required modules if run only via --run at90797 (runtime
source is pinned separately; no .olean emitted by --run). NEPAudit requires an
ordinary focused compile before that runtime. No compiled Stream A objects used.

Checkpoint correction: previous receipt-staging commit failed because a quoted
git directory glob did not match untracked directories. This commit stages
finished receipt paths explicitly. Through90709 all targets pass except90701;
10/60 Lean used (9pass,1fail),2/10 native,0Kani. Driver19289 still active through
ParserTransport. Next90710 ParserFlat. Corrected BytesSource90708 and
ParserWindows90709 both PASS. Raw wrapper now supports reserved90797 via
`python3 tools/pv-rdcd7-20261102/lean.py 90797 R1Z/PV_RDCD5_NEPDriver --audit-runtime`,
including dynamic consumer-root dependency fingerprint and helper source pin.
NEPDriver remains runtime-only, exclude it from object-required coherence.
Focused90798 now queries actual native_window rather than only owned cm_window.
Supplemental textual reference scan97733 is5/9 complete.

## Session 2 recovery

Resumed after lead stopped the stalled session. First command was git status.
RESUME-SESSION2.json reconciles every local receipt with all host attempt
directories and exact host time/output/barrier files: identical, no live scope
or task process. 90700–90713 and N90800–N90801 spent; 14/60 Lean (13 pass,
1 elaboration failure),2/10 native (1 pass,1 preflight failure). Next90714;
46 Lean/8 native remain. All previously untracked evidence committed b90bdbdb4a.
Driver now resuming90714 through ParserTransport; do not duplicate it.
The inherited prompt-pv-rdcd3.txt remains missing; no new scope/rule inferred.

## Session 2 final checkpoint — writer confirmation required

Read SESSION2-HANDOFF.md first. Unexpected overlapping commita520a3515c appeared
at22:47:40 during the resumed session; user clarification is pending. Driver
PID72404 was stopped before90716 retry. No live host scope;90716 is UNSPENT
(pre-upload reservation refusal only). Spent90700–90715:16/60 Lean (13pass,
3elaboration failures);2/10 native;0Kani. Remaining44 Lean/8 native. Receipts,
refreshed live-ref census and complete checkpoint committed2ec7e0e75c.
The source-resolution plan is stale after unexpected ParserComponent import
changes. Refresh and stage it only after writer coordination, then compile
ParserComponent before ParserTransport. No V197 restoration/release claim yet.

## Session 3 active checkpoint

User explicitly confirms ONLY writer. RESUME-SESSION3.json reconciles all host
receipts, no inherited live scope. Accepted ParserComponent split; refreshed
stage plan contains26 modules. 90716 and90717 failed elaboration (Option match
metavariables;90716 also residual rfl). residual_none now checks without sorryAx
at90717. Current source binds converted array locally before matching; not yet
compiled. Driver exec13731 queues90718 through ParserComponent. Two pre-upload
reservation refusals so far;90718 UNSPENT, waiting full180s and retrying same ID.
Do not duplicate driver/scope. 18/60 Lean used (13pass,5fail),2/10native,0Kani.
Next after90718 result: fix if needed, or compile transport then consumers.

CONSUMERS-session3-refresh.json preserves15 extra live-ref revisions and44
variants; all added model variants on this branch/remote, no new consumer on
other branches. CONSUMERS.md includes ParserComponent. New association draft
V197-ASSOCIATION.json is PENDING. source-proof-precheck.json is syntactic only.
check-release derives current51 raw roots (old hardcoded47 label fixed).
No restoration or release claim yet. Current sole writer made commits through
2862e1a9bd; no merge/push. All original compiler/runtime/observer qualifications
and unchanged endpoint/T boundaries remain.

### Session 3 continuation after component verification

90718 failed only the implicit range continuation (conversion/residual pass).
90719 ParserComponent PASS, complete eight queried lemmas, standard axioms only,
wall3.25s RSS2470420KiB swap0. 90720 ParserTransport FAIL: ambiguous root vs own
bind_congr; now all applications fully qualified, source changed/committed.
21/60Lean spent (14pass,7fail);2/10native;0Kani. Driver exec51764 queues90721
through ParserTransport; one pre-upload aggregate refusal,90721 unspent.
ParserTransport's late continuation and Restored.native_window are explicit
using the checked component helper. All source changes committed c818142230.
op71-consumer-binding.json pins exact existing dictionary callback text and
qualification; no whole dictionary compilation. After transport succeeds,
refresh stage.py plan/source hashes before compiling through NEPAudit. Reserved
90797/98/99 unspent. HANDOFF earlier driver13731/65601/19553 are FINISHED.
