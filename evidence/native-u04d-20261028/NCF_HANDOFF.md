# NCF U04 continuation handoff

S2 OPEN; deployed 100-bit target not yet established. Branch
codex/cx-native-u04d-20261028. All fourteen whole slots remain OPEN.

## Established components

- op29/op30 actual native contracts on full typed entries/every u64 slot, their
  inverse postcondition controls and local stub_verified use/control pairs:
  K002–009. NCF_EntryContract.op29_exact/op30_exact match the cohort Bool
  predicate without changing NBX's candidates. These are local contracts and
  values, not whole SDK extraction components.
- Five decoder wrong-length pairs on symbolic valid lengths, zero-initialized
  backing with one arbitrary byte at arbitrary offset: K010–019. Exact domain
  and arbitrary-payload gap are in NCF_STAGE2_FINDINGS / NCF_PAYLOAD_FINDING.
- One selected mutable iterator row/write/frame: master K020/K021;
  checkpoint corrected K024/K025. K022/K023 excluded for an own wrong capacity
  constant. These selected nth fragments do not prove the original decoder's
  iterator prestate/next association or its full loop.
- Box component checks K030–045: arbitrary complete typed master/checkpoint,
  arbitrary initialized field/array coordinate, two runs on identical typed
  arguments, ambient coordinate preservation, distinct simultaneously live Box
  allocations, and surviving Box preservation after the other is dropped.
  Eight positive checks pass, eight inverse controls fail in exact KMX config.
  These do not replace native decoders or prove account/Box caller composition.

All NBX/NCC modules/evidence are reused; no old theorem is re-proved. New proofs
only: NCF_EntryContract, successful L003; standard axioms
propext/Classical.choice/Quot.sound. New source contains no sorry/axiom/admit or
native_decide/heartbeat/depth override. L002 failed elaboration (no credit),
L001 submitted transport unresolved (never resubmitted). The corrected L003
source differs from both predecessors. Exact receipts/pins retain each attempt.

## Open components and next steps

The bridge table is authoritative for each slot. No AeneasExtraction component,
headline input, cryptographic assumption, runtime trust item or security metric
is discharged/changed. The native actual authentication call-site association
is still open for all slots. Reached callee domains must be proved on the SAME
native caller execution; independent native getters or a model projection do
not establish that association. Intervening PDA/decoder/borrow/allocator calls
must use CLOSED bridges in their domains; no arbitrary successful replacement.

The arbitrary-payload allocation contract is unusable: K026 CAR-size failure;
K027 has both a postcondition and CAR failure; K028 is a mutable-slice
stub_verified compiler ICE. None is a valid control/pass. Unexecuted
arbitrary_long candidates have no credit. The one-window rejection domain is
reported explicitly, not silently promoted to every byte slice.

## Resources and freeze

One admitted capped scope at a time: MemoryHigh6G/MemoryMax8G/Swap0/Tasks64,
Lean -M7000, Rust opt-level3, 90s Kani solver gates. Complete frozen dependency
package+edge validation offline before each Kani run and unchanged lock after.
No --locked passed to cargo-kani. Exact KMX patch
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67;
stub ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.
No custom copy/field multiplication/SHA implementation stub. No timeout or
memory kill so far; no cap increase. Source snapshots and source-versioned
patches are retained. Formal/native section-6 fields are in NCF_ATTEMPTS.jsonl
and each receipt; printed failed-theorem placeholder axioms are excluded.

Repository crates/programs/Cargo.toml/lock are unchanged. Harnesses and
cfg-only annotations live solely in inherited owned host scratch, committed as
patches/receipts. No shipped change or SBF rebuild trigger. Inherited ELF pins,
not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Cache retained: /home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028.
SInt2/library objects read-only; imported cache and 219 resolved Aeneas objects
pinned in L003-object-pins.json. No wallet/key action, other worktree/candidate
edit, binary/object/ELF commit, push or merge. Budget/final audit follows below.

## Final contract/caller audit and stop

Budget **70/70 Kani**, **3/60 Lean slots charged** (two actual compiles plus
L001's unresolved submission). All70 native receipts are terminal. No further
Kani launch is authorized. Raw audit:24 local positive components,30 intended
single-failure semantic controls,4 provisional positive checks,12 excluded runs.
NCF_AUDIT.json is mechanical and retains every failure, resource field and axiom
line. None of the four provisional checks counts as a closed bridge.

op25–28 individual postcondition inversions and local contract-use/assertion
controls K046–057 were added around the unchanged native getter contracts;
NCC K055–058 callee body proofs are reused. The actual SDK callers remain open.

op15's exact conditional native policy contract K058 passes. K060 cannot compile
until a cfg-only Arbitrary implementation enumerates all eight real error
variants; corrected K061 passes, K062 fails its caller assertion. Program K063
has a cfg-only KMX alloc-registration compile error; K064 then exposes that
Kani does not recognize only the dependency crate's proof_for_contract harness.
A program-local foreign-function proof is admitted and passes in K065. Actual
unchanged SDK authentication K067 passes3143 checks (240 unreachable) in the
restricted rejected/aliased account fixture, with the policy contract checking
its expected-field pointer. K068 fails its intended Result assertion.

**Controls K059 and K066 are INVALID:** each fails both the intended inverse
postcondition AND the native policy's ghost pointer precondition. The inverse
wrapper did not establish the callee's domain. All op15 conditional-policy and
SDK pilot bridge credit is therefore withheld, including K058/K061/K065/K067.
This corrects the earlier optimistic description of those control results.
The ghost precondition is also not established for every upstream caller and
is a finding, never a new release hypothesis. The fixture does not cover the
parent's accepted unique/readonly-account domain. NCF_SDK_PILOT_SCOPE.md gives
the exact limits. NCF_policy_control_fix.patch is prepared but UNEXECUTED;
it requires a new authorized Kani allocation and its own controls.

K069/K070 independently check the ACTUAL master Box decoder wrapper's exact
wrong-length InvalidAccountData mapping on valid symbolic-length one-window
inputs; positive passes, inverse fails. The remaining decoder/iterator/Box join
is not inferred. Program checkpoint/ASQ8 rejection candidates and the wrong-
pointer diagnostic were not run and receive no credit.

## Member-by-member native blockers; no remaining independent Lean-only gate

| Slot | Exact remaining obligation requiring new native/P6 evidence |
|---|---|
|15| Repair both policy postcondition controls; remove/establish the ghost precondition on every upstream caller; accepted-domain actual authentication association and extraction component. The rejected/aliased pilot is insufficient. |
|23| All-payload arbitrary-length rejection transport and actual validate_asq8 child call on the same instruction suffix/returned request. Weak mutable-slice input generation failed; bounded/one-window checks cannot supply it. |
|25| Same decoded V1 registry at actual authentication paused call; actual caller domain/return-use association through prior decode and PDA calls. |
|26| Same V1 registry at authentication immutable call. NCC private-validator and NCF local use controls are not that point. |
|27| Same decoded V2 registry in immutable-deployment authentication branch at paused call; prior PDA/decode domains. |
|28| Same V2 registry at immutable call and same native continuation, not an independently chosen record. |
|29| Actual V2 entry/current_slot authentication point after decode/PDA; exact native-to-cohort extraction component. Local full typed contract/value is already checked. |
|30| Actual V1 entry/current_slot authentication point after decode/PDA; exact extraction component. Local full typed contract/value is already checked. |
|31| All-payload larger-length rejection plus actual borrowed V1 registry bytes, Result/error mapping and SDK point. |
|32| Same obligations for V1 entry account bytes. |
|33| Same obligations for V2 registry account bytes. |
|34| Same obligations for V2 entry account bytes. |
|48| Original decoder representability on success, original iterator prestate/next and actual read/write association, validation, account/Box/error/allocator frame and authentication caller. Selected nth, typed Box and one-window wrong-length checks are separate components only. |
|49| Original checkpoint decoder/iterator and canonical digest, successful/error paths, Box/allocator/account frame and same authentication caller. Typed Box/selected row components do not discharge these. |

Every remaining fact above is a native execution/association boundary, not a
missing pure induction/selection lemma. All independent NBX frame, sequence,
capacity, result, candidate-installation and retention lemmas are imported
unchanged by NCF_EntryContract through NCC_ReuseAudit; the new scalar contract
value equations compiled with standard axioms. Re-proving those lemmas or
assuming the missing native conclusion would not discharge a row. Thus Kani
exhaustion leaves no independent Lean-only obligation to execute under this
allocation. Next deliverable: corrected op15 controls followed by an actual
accepted-domain call-point bridge with its callee domains proved; alternatively
an input representation supporting all-payload symbolic-length rejection.

## Final provenance, retention and resources

L003 target NCF_EntryContract.lean: exit0, wall2.368627096s,
peakRSS5,617,008KiB, swap0; source revision c8f2812dbff5041f3eda200c002b670ba6d8666c
plus the exact dirty-source hash in its receipt. Both printed theorems use only
propext/Classical.choice/Quot.sound. This is focused validation against the
pinned inherited objects, not a full frozen-release manifest replay.

NCF_HOST_FINAL.json verifies all585 imported private-cache files and all219
resolved Aeneas objects unchanged; retained cache now has586 files, adding only
NCF_EntryContract.olean. All70 native attempts and final batch are terminal.
Own2,507,476,336-byte NCF_target and empty NCF_tmp were removed. The persistent
lane cache, inherited sources, receipts and snapshots remain; no other job's
output or cache was removed.

The host compares498 frozen tracked source/manifest files:491 unchanged and
seven expected cfg-instrumented parent files (four inherited parents plus
three new parent locations). Removing only NCF's registrations/annotations
reproduces the exact retained NCC_K060 parent bytes or frozen originals.
NCF_final_harness.patch and NCF_final_sources reproduce all own executed
instrumentation; NCF_FINAL_PATCH_PIN.json pins the patch and exact base.
Tracked repository crates/programs/Cargo.toml/lock remain byte-identical to
frozen source (NCF_FROZEN_SOURCE.json). No shipped implementation changed.

Own final metadata command experienced five SSH255 resets at300732 inline
bytes. The same validation was delivered through stdin and succeeded; no
proof was resubmitted and no shared infrastructure was changed. The aborted
metadata client and transport repair are recorded separately. All earlier
proof transport recovery is preserved; L001 remains unresolved, never reused.

No file exceeds20MB; no binaries, .olean, ELF, tarball or private keys are
committed. No full unchanged regression, cap increase, solver timeout, memory
kill, SHA unwinding, field multiplication gate, session-A worktree/candidate
edit, push or merge occurred. Inherited release ELF hashes are not newly
reproduced. The deployed100-bit target remains not yet established.
