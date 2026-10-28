# NCV decoder handoff

**Partial result; op48/op49/op50 native bridges remain OPEN. S2 and the deployed
100-bit target are not established.** Both job allocations are exhausted:
60 Kani,60 Lean;10 separately capped extraction attempts. No further prover run.
Branch: codex/cx-native-decref-20261028. No push, merge, shipped Rust change or
session-A worktree/candidate edit occurred.

## What JHr can use

The complete safe Rust reference is NCV_reference.rs (E008); the exact extracted
bodies are delivered in lean/NCV_Reference/{Types,Funs}.lean. All three functions
include their actual format/canonicality/state checks and rejection behavior.
NCV_Carrier gives lossless nominal record conversions; NCV_Install assigns the
converted functions to AdapterRw.Ops op48/op49/op50 and preserves the outer
Aeneas failure/divergence layer. Inner Unit errors become InvalidAccountData.

`NCV_InstallationSupport.configure missing` is exactly
`{missing with adapter := NCV_Install.install missing.adapter}`. Its sdk_master,
sdk_checkpoint and sdk_lane theorems prove the SAME selections survive
DrvC_Installation.sdk. It imports NCF_EntryContract/NCC_ReuseAudit read-only and
reuses NBX_SequenceResult.returned. These are checked dictionary selections and
representability facts, **not** new AeneasExtraction/P6 instances.

E010's separate NCV_CastRef uses safe field casts. It emits no external template
and has the symbolic field/fixture support below. E009's unwrap_failed template
is excluded; its raw template is .txt evidence only. No old native result is
reassigned to E010, and no unproved equivalence between the variants is claimed.

## Native evidence and limits

K002/K003 are the exact-KMX copy positive/failing control. Wrong-length actual
wrapper/ref body contracts have matched inversions at lengths383/385/0(master),
191/193/0(checkpoint),767/769/0(lane): K006–023. These cover arbitrary complete
payloads at those lengths, not the accepted account lengths.

K045/046: actual decode_pool_identity_v1 equals the reference on EVERY144-byte
input, with error variants collapsed to Unit (sufficient for the enclosing map).
K047/048: actual validate_verifier_policy_v1 success/rejection equals valid_policy
on EVERY full typed policy. This does not identify its individual error variants.
Both are ordinary body comparisons with single-assertion failing controls, not
verified call-site substitutions or enclosing-call associations.

K049–060: six paired four/eight-byte, sequence-write/frame/capacity and lane
frontier/final-empty-root fragment checks. Each uses arbitrary window/pre-state
values in its stated domain. They do not prove the original iterator's pre-state
association. NCV_CopyFrame composes KMX value laws, arbitrary offsets, disjoint
row windows and outside framing; actual pointer/allocator/caller association is
still a separate gate. No field multiplication or SHA syscall was unwound or
stubbed. No Option<fn> credit or stub_verified Box substitution is used.

K004/K005/K024/K025/K026 timed out; never credited, raised or rerun unchanged.
All full-buffer header shapes were retired. K027–044 selected no harness due an
own validator variable collision:18 excluded, charged invocations. The corrected
validator asserts actual/requested target equality; see NCV_RUNNER_FINDING.md.
Native totals:18 local positives,18 intended negatives,5 timeouts,19 setup/target
failures. These classifications are not decoder closure counts.

## Kernel results and fixture status

NCV_L060 audits34 accepted modules,111 new top statements and all six decoder
definitions: exit0,wall2.203949165996164s,peakRSS5607200KiB,swap0. All117 printed
audit lines contain only propext,Classical.choice,Quot.sound (or a subset).
Exact source revision, hashes, target, argv and dependency pins are in receipts.
All219 actually resolved Aeneas objects match the coherent SInt2 selection.
This is a focused closure audit, not a full frozen release replay.

The CastRef model has symbolic zero/equality scans, checked field/word laws,
array-frame induction, complete sequence and canonical digest assembly, sequence
validation, caller geometry and one frontier step. Actual fixture evaluations:
all eight master/checkpoint sequence rows(L045); checkpoint root, lane root and
all20 frontier digest reads(L050); counter43/checkpoint42/lane-index13(L058).
There is NO complete decoder observation for JHj. The attempted full frontier
loop bridge failed elaboration at its size literal (L055/L056,"No goals to be
solved") and is excluded in NCV_drafts. No error-placeholder axiom is accepted.

## Remaining, member by member

| Decoder | Native/P6 work requiring a new allocation | Remaining Lean fixture work |
|---|---|---|
|op48 master|Full384-byte wrapper equality; policy decoder/header association; original row/validation loops; same-input callee domains, error map and fresh Box/context frame. Identity and policy-validator local checks do not compose these automatically.|Identity/policy/header/nonzero/chronology assembly and final returned record. Sequence/counter subobservations are already proved.|
|op49 checkpoint|Full192-byte wrapper equality; original iterator read/check association and complete capacity rejection behavior; canonical-digest caller association; error map and Box/context frame.|Header/master/domain/nonzero checks and final record assembly around the proved digest and sequence fields.|
|op50 lane|Full768-byte wrapper equality; original20-step iterator/digest/empty-root association and error map/Box frame. Local guards and point reads do not establish it.|Repair and instantiate the frontier loop bridge, discharge occupancy/empty-table rows for index13, then header/key/field assembly and final record.|

All three also retain the existing runtime/heap/ABI/std/source-to-ELF boundaries.
The headline remains AspisR1.RPx_Deployed.deployed; no game, metric, quantifier,
trust item or source-refinement hypothesis was changed. L154 and narrowed D188
remain as approved. No XRn join kit/stand-in was used.

## Delivery and cleanup

NCV_DELIVERY.json maps35 canonical lean/ files to byte-identical checked source
hashes. Failed drafts/API probes are separated; immutable attempt snapshots stay
in evidence. NCV_ATTEMPTS.jsonl and NCV_VALIDATION.json preserve every disposition.
Native harnesses are delivered as NCV_harness.patch plus versioned input-source receipts; top-level raw harness modules are not shipped.
Static Cargo.lock/KMX sources are referenced by frozen git/patch hash and remain
in the host attempt snapshots; they are not duplicated60 times locally.

Host: /home/dombarker/project-offloads/codex-cx-native-decref-20261028.
Retained cache: /home/dombarker/project-offloads/codex-cx-decref-cache-20261028;
NCV_POSTFLIGHT.json pins all retained objects. Imported caches were copied, never
modified. All496 frozen source paths are accounted for; the two scratch edits
strip exactly to frozen bytes and contain only cfg(kani) support. Source/library/
cache checks pass. Owned Rust/solver/compiled-object scratch was removed after object copies were verified; source and cache remain.
No keys were generated or cleaned up. No ELF rebuild trigger occurred. Inherited,
not newly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
