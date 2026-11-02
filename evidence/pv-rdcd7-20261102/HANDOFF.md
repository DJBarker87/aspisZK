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
