# NCC U04 method pilot handoff

PILOT RESULT: **contract mechanisms are usable for the tested pure Bool/record
interface on Kani 0.67.0 / CBMC 6.8.0.** All three required negative controls
fail at their intended postcondition, caller assertion, or assignability check.
Direct-body baselines pass; four actual getter contracts pass; the unchanged
native V1 validator caller passes under verified is_immutable replacement, with
its matching inverted-assertion control failing. Details/receipts:
NCC_CONTRACT_PILOT.md, NCC_PILOT_CONTROLS.json, K035–040 and K055–060.
This is not a general theorem of tool soundness or the SDK authentication join.

**All fourteen U04 whole-slot instances remain OPEN. S2 / deployed 100-bit target
not yet established.** NCC_U04_BRIDGE.md contains one row per slot, exact native
arguments, local evidence, and remaining native obligation. No row is marked
"instantiated by native function (ruling s)".

## Established / scope

- Six actual getters and the policy validator: two runs on equal complete typed
  arguments (plus slot), independent ambient states, observation of every
  initialized field and array coordinate; matching one-byte input-change controls
  fail. K041–054. Padding/invalid references/concurrent mutation are not admitted.
- Four registry/entry decoders and ASQ8: complete Result equality/error and
  arbitrary backing-byte frame with independently varying bytes outside the
  passed prefix. K025–034. Exact domains: lengths 0..129/193/257/321, ASQ8 0..321.
  No caller bound is silently added; NCC_DOMAIN_FINDINGS.md records the gap.
- Native V1/V2 flag getter contracts K055–058 have requires(true), exact Bool
  postconditions, default readonly frame. The actual unchanged private validator
  consumes the replacement and preserves its complete rejection/return behavior
  (K059/K060). This caller is below op31, not the SDK authentication op26 point.
- NBX/NBU/NBN modules, headline candidate installation/retention and row/read/
  predicate/domain induction are reused unchanged (NCC_IMPORTS.json). No abstract
  adapter law, unverified decoder/allocator replacement, new trust or XRn kit.

No headline extraction premise is discharged. No native loop/Box composition
is manufactured from local induction. The field/crypto/model/security metric,
headline RPx_Deployed.deployed, frozen3, L154 classification, D188 narrowing and
runtime trust list remain unchanged. No new LPb passing stage is credited.

## Validation / failures / resources

Kani **60/60**: 27 PASS, 23 semantic counterexamples (20 matching negative
controls and three machinery controls), ten excluded unwinding failures.
NCC_AUDIT.json checks statuses, exact KMX/stub/lock hashes, complete graph,
limits, source/config matches and each paired control. NCC_SOURCE_VERSIONS.json
matches all 60 native source hashes to retained complete local snapshots.

K013–020/K023–024 failed the harness's memcmp unwinding check; 245–812 properties
were undetermined. They receive no proof/control credit. Guarded indexed
argument-equality constraints replace that harness loop; no native decoder body
or resource bound changes. No solver timeout, memory kill, cap increase,
unchanged timed-out replay or full frozen regression occurred. Runtime-formatted
assertion-message/unsupported-construct warnings remain in the full logs;
K038/K060 fail at the intended comparison panic, with successful baselines and
no additional failed properties. No warning is suppressed.

Every actual run: one capped scope at a time, MemoryHigh6G/MemoryMax8G/
MemorySwapMax0/TasksMax64. Rust opt-level3; 90s solver gates. Before every Kani
run, complete frozen package+edge validation offline; lock hash unchanged after
every run. Exact KMX patch bcdf749b... and actual stub ad8efb63...; no custom copy,
field multiplication, or SHA implementation stub. Kani/CBMC binary hashes are
pinned in every later stdout and the pilot control audit. No cargo-kani --locked.
NCC_ATTEMPTS.jsonl and per-attempt receipts retain target/command, revision,
source/dependency/tool pins, exit/wall/RSS/swap/cgroup and N/A native axiom audit.

Transport: quiet-window admission refusals wait/retry, never launch. K002–011
were recovered read-only after an SSH output loss; absent K012 was submitted
once. Own serialization/collector/controller repairs preserve shared launchers,
reservation and validation. L001's combined setup/submission lost SSH; read-only
recovery found no host setup/source/config/receipt/job. It is retained without
validation credit and never resubmitted. The new 54-root NCC_ReuseAudit target
has a separate source and attempt; final Lean receipt is appended below.

## Remaining / why further Lean alone cannot close it

- op15: actual authentication caller's policy argument/carrier and return use.
- op25/26: same decoded V1 registry in ONE native authentication execution at
  SDK op25/op26. The private validator context is insufficient.
- op27/28: same V2 registry/call points in the real immutable-deployment branch.
- op29/30: same native decoded entry/current_slot and SDK reached getter points.
- op31/32/33/34: larger-length rejection plus native account-borrow arguments,
  Result/error mapping and caller association at the corresponding SDK points.
- op23: arbitrary suffix length/rejection and same request/child arguments in
  the actual parent, not merely a bounded two-run decoder.
- op48: actual original reader/iterator and validation, real Box/error/allocator
  frame and authentication caller. NBX's sequence/capacity induction is retained.
- op49: actual reader/iterator/canonical-digest, Box/error/allocator and caller.

Each remaining member needs new native/P6 evidence. Existing independent Lean
selection, continuation, value/frame induction and bounds are already supplied
by NBX and are not re-proved or repackaged as a missing conclusion hypothesis.
Kani exhaustion therefore permits no further native launch. The useful next
unit is the actual authentication continuation under the now-checked getter
contract, with the same decoded-record prestate and real lower-call domains.

## Reproduction / freeze

Owned inherited scratch: /home/dombarker/project-offloads/codex-cx-native-tx2j-20261028/NBU_src.
Retained owned cache: /home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028.
NCC_CACHE_IMPORTED.json pins all584 initial files. Coherent SInt2 objects remain
read-only. Final resolved Aeneas/library/cache and cleanup manifests are recorded
separately. Own cache is never deleted.

Start frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 and frozen Cargo.lock;
apply the exact KMX patch/crate registration and inherited NBU/NBX patches,
then NCC_stage3_harness.patch. It contains only scratch cfg(kani) registration,
new NCC module and cfg_attr(kani) getter contracts. Stripping those annotations
reproduces the previous scratch source exactly (NCC_CONTRACT_INSTALL.json).
NCC_PATCH_PINS.json pins all own patches; older snapshots/patches reproduce
prior stages. Prepared unexecuted contract candidates receive no native credit.

Repository crates/programs and Cargo.toml/lock remain byte-identical to frozen
source. No shipped-file or SBF rebuild trigger. ELF pins inherited, not reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No wallet/key action, session A worktree/candidate edit, other worker prefix
edit, binary/object/ELF/archive commit, push or merge.

## Final focused Lean reuse audit

NCC_L002 / NCC_ReuseAudit: exit0, wall2.125393630s, peakRSS5,580,244KiB, swap0; source revision bb2ac643ca24facb072417224e2b6a15552ed182 plus the exact dirty source hash in its receipt. All54 inherited NBX roots use only propext/Classical.choice/Quot.sound or none (NCC_AXIOMS.json). All NBX modules are imported without re-proving them. No new theorem, slot witness or extraction premise discharge is added. Actual resolved Aeneas objects are pinned; this is a focused reuse audit, not a new release manifest replay.

Budget: 60/60 Kani; one successful Lean compile, with two submission slots conservatively charged out of60 (L001 transport/no host setup observed; never resubmitted). Every remaining row above requires new native/P6 evidence, so there is no independent new Lean-only closure left to attempt. No further Kani launch is authorized.

Final retention/freeze: all584 imported private-cache files and all219 resolved Aeneas objects remain unchanged; the retained cache now has585 files, adding only NCC_ReuseAudit.olean. No own prover/controller is live. Own1,765,790,485-byte Rust target and empty temporary directory were removed; cache, source snapshots and receipts remain (NCC_CACHE_END.json / NCC_CLEANUP.json). Final repository audit confirms all496 crate/program files and root Cargo.toml/lock equal frozen source; host audit confirms492 unchanged files plus the four exact cfg-instrumented parent hashes used by K060 (NCC_FROZEN_FINAL.json / NCC_HOST_SOURCE_AUDIT.json). No evidence file exceeds20MB, no binary/object/ELF is committed, and no wallet/key operation or push occurred.
