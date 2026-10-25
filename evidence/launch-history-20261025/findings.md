# Launcher history: immutable evidence only

Scope: branch `codex/cx-launch-history-20261025`, frozen examination base
`eccc7281331722dca97dfaf7cd605478169abacf`. No host action, compiler, live worker
file, external cache, key, or other worktree was accessed. Historical paths below
are provenance, not instructions to access them. This is a forensic receipt,
not proof validation or launcher implementation.

The committed record does **not** establish that the old Lean launcher stopped
working. It establishes later successful Linux Lean invocations, some real
Linux import failures in a changed dependency environment, and separate failures
in new metadata/setup tooling before a whole-consumer proof ran. The latest
success must be reported within the examined scope, not as a global latest
across all branches.

## Answer to “why ten hours; why did the old one stop?”

There is no evidence here of ten hours spent fixing the same broken launcher,
nor a complete time-accounting record for those ten hours. There is evidence
of several different jobs becoming conflated: focused cached theorem compilation,
raw declaration compatibility/reconstruction, a new whole-consumer loader, and
privacy native-gate metadata admission. Their failures are real, but they occur
at different layers and are not interchangeable evidence about an old launcher.

**A material path mismatch:** the committed `joint-drive.py.txt:63` and
`joint-drive-range.py.txt:66` call
`/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh`.
The October 25 probe tested the different literal path
`/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/run-joint.sh`.
ENOENT at the second path does not establish absence at the first, deletion,
or a failed invocation of the historically used script. No further query ran.
The probed missing `lean-toolchain` at that same historical workspace root also
does not establish failure of later launchers, which write their own toolchain
file and call an absolute Lean 4.32 toolchain path in separate job workspaces.

## Latest verified successes in the examined receipts

`receipts.json` records 160 committed `lean-*/receipt.json` files from the fixed
Port7CLEAN/13GATE/15DRIVER/16CUT/17RELEASE/18–28 families, their commands and
statuses, plus selected complete receipts, source hashes, admission summaries,
full axiom lines and immutable blob hashes. It is not an inventory of all Git
branches. October 25 Port29 diagnostic receipts were additionally inspected:
their actual commands are Mac paths. Released A packet lead reviews contain
later successful focused validations, but summaries lacking actual host commands
cannot establish Linux execution; no A candidate files were inspected. The
allocation's `A24798` shorthand was not resolved to a concrete host receipt in
this bounded examination. No global-latest claim follows.

| Kind | Latest established in this scope | Evidence and limitations |
|---|---|---|
| Successful Linux Lean invocation | Port18COHERENCE `lean-011`, `RootSnapshot` | GO admission timestamp **2026-10-24T17:30:22.074292Z** (18:30:22 BST), exit 0, 10.892868341s, GNU time RSS 1,650,992 KiB, swaps 0. Raw diagnostic IO, **not a theorem or release**. |
| Successful Linux theorem compile | Port17RELEASE `lean-013`, `Control` | Admission timestamp **2026-10-24T16:12:12.263767Z** (17:12:12 BST), exit 0, 5.178198348s, RSS 4,435,952 KiB, swaps 0. Three standard-axiom reports. Conditional source-model control bound, not concrete remaining budgets/security closure. |
| Intermediate later diagnostic | Port17RELEASE `lean-024`, `Compatibility` | Admission 2026-10-24T16:32:56.563338Z, exit 0, 1.407105382s, RSS 2,590,280 KiB, swaps 0. Reported structural differences; success of the scanner is not compatibility success. |
| Historical coherent manifest | October 19 manifest-2 completion | `462 of 462 current`, beyond the earlier 402-module D65 build. Historical selected closure only, not today's whole consumer or frozen release gate. |

Timestamps above are **actual admission receipt timestamps**, not invented
compiler start/end timestamps. Commit dates are different again: RootSnapshot's
receipt was committed by `63204ebb6d44771353b790806a46b2448abca1d0` at
2026-10-24T18:52:43+01:00. Its `source_revision` field is the dirty checkout
baseline `9d37baa7dc8a0b2a7733288f0477cc3e47234a9b`, not a claim that this
baseline commit contains the executed new source. The snapshotted source hash
is `79dff90f82626624adbf796ad1e0259b402949d3dba5b7f8f3827d0edb53ed33`.
Port17 Control similarly records dirty baseline `b454e7d6d930889e30aded35f8f2466344f2148c`,
with exact source `6243ac8d47632ffe69704aeee4be990168b624192e4fdb3cc81669d6105b4bd8`,
and receipt publication in `1586ea11eb72aa0d4ebde85ac86cc61d1a55f1e4`.
These receipts are ancestors of the frozen examination base, not new identity gates.

### Exact successful Linux route

RootSnapshot recorded:

```text
cwd=/home/dombarker/project-offloads/codex-cx-port18coherence-20261024
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M4400 -DElab.async=false -o Port18COHERENCE_RootSnapshot.olean Port18COHERENCE_RootSnapshot.lean
```

The committed `tools/port18coherence-20261024/Port18COHERENCE_compile.py`
constructs this host command (historical command reconstruction, not execution):

```text
cd /home/dombarker/project-offloads/codex-cx-port18coherence-20261024 && flock /tmp/aspis-r0-lean.lock sh -c 'python3 Port18COHERENCE_admission.py > lean-011-before.json && python3 Port18COHERENCE_admission.py > lean-011-go.json && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port18COHERENCE_run_host.py lean-011.json'
```

`run_host.py` verifies actual scope controls, snapshots source, then uses
`/usr/bin/time -v -o <attempt>/time.log timeout 180 <recorded command>`.
Both admission snapshots report reserved 26,172,456,960 B (24.375 GiB),
additional 8 GiB, limit 55 GiB, admitted true. The scope reports exact
6G/8G/Swap0/Tasks64. Its `memory.peak` is 343,805,952 B; retain this separately
from GNU time RSS, without silently reconciling the differing values.

Dependency identity: full `LEAN_PATH` is preserved in the selected receipt;
`input.tsv` SHA is `d0ca07d618dd4e447c664a3327c9475cfa9a72cc72dbea2e541c6a5b01b8524a`.
**Receipt limitation:** its `lean_binary` text says “recorded in host receipt”,
but this receipt does not actually supply the binary hash or full runtime closure.
Do not fill that gap from another run. `print_axioms=[]` means this raw `#eval`
diagnostic printed no theorem audit; its formal result is **N/A**, not axioms-free
proof. Full source uses raw module-data traversal, opaque proof dependencies,
and region release; it does not establish declaration validity by scanning.
The committed compile/run-host source was introduced at `63204ebb6d` and has
no subsequent change before the examination base. Its exact blob SHA/size is
retained, but the historical receipt does not bind the wrapper's executed bytes
by hash; the launcher chain is a committed source reconstruction with that
explicit limitation, not a new execution attestation.

For the theorem route, `Port17RELEASE_compile.py` holds the same global lock,
takes fresh admission, creates the independently capped scope, then runs
`Port17RELEASE_lean_host.py lean-013.json`, which pins selected import objects
and writes `lean-toolchain` before `Port17RELEASE_run_host.py` executes:

```text
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M4400 -DElab.async=false -o Port17RELEASE_Control.olean Port17RELEASE_Control.lean
```

Recorded Lean binary SHA:
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Direct Cuts object SHA:
`45f7f441e359c2d52bd6874b88750f56f2cbe27c53531c0c3e72fa8e3eb72cbc`.
Frozen full-object manifest is represented only by size 5,673,109 B and SHA
`ac51d9e78c25c0183b62b43776cb126b24a2c567f7724220ceb3fd37cb7e1079`;
its external bytes were not read. Inherited receipt SHA and all direct source
pins are in `receipts.json`. This is selected cached-dependency provenance,
not a coherent whole textual-source rebuild or complete runtime identity.

Full recorded theorem audit:

```text
'AspisR1.Port17RELEASE_Control.next_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.Port17RELEASE_Control.stages' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.Port17RELEASE_Control.rust' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These retain `ops`, `reserved`, `unwrap`, arbitrary `rest`, weights and
`ReleaseBudgets rest w`, Digest32/hash, arbitrary inputs/state/oracle;
`stages`/`rust` bound log length by `1046 + delegatedWeight w`. They do not
instantiate all native/source per-operation budgets. No premise was changed by
this job; before/after statements are identical because no theorem was edited.

## What changed, and what actually failed

1. **Old October 19 route:** driver invokes `H/tools/run-joint.sh <attempt>
   <module/path> J 7000 7 <fingerprint>`. Script defaults to MemoryHigh5G,
   MemoryMax7G, Swap0, **Tasks128**, slot locks in-window/global lock outside,
   an older incomplete reservation traversal, and manifest-ordered source/object
   dependencies. October 19 `joint-attempts-5532-5547.jsonl` ends with actual
   green PrivacyR1P5547: 1.77s, RSS3,608,652KiB, swap0, source
   `0782a767e476cd7d6e1de07f0e86fe5cbacef65c36939572032a5f858c7b86e2`,
   dependency fingerprint `bdfd1bbbaddd2fdd`, two full standard-axiom lines.
   Completion records 462 current modules but also two internal SamplerWordRead
   reports using `core.fmt.Formatter`; root reports are standard. This historical
   closure is not certified under today's only-standard-axioms release policy.
   **Do not adopt this old script unchanged:** task limits/admission differ.
2. **October 24 focused route:** separate job workspace, absolute Lake4.32,
   `-M4400`, fresh 6G/8G/Swap0/Tasks64 scope and global lock. Port7's earlier
   admission scanned only scopes outside its lock; Port13 onward records the
   corrected whole hierarchy. Historical aggregate caveats remain, rather than
   retroactively upgrading Port7's evidence.
3. **Actual Linux failures do exist, but with changed inputs:** Port17
   `lean-009/010` exited134 on import/interpreter memory exceptions with the A
   dependency overlay at `-M4400`. Root-only changed-environment Control013 then
   succeeded; no larger cap retry. Port18 `003/004` also failed memory-heavy raw
   import/region retention; changed region-releasing traversal succeeded007/011.
   These demonstrate target/environment-specific failures, not a broken SSH or
   stopped general launcher. Port17 diagnostic024 found 111 of 246 compared
   modules structurally different in a 7707-module graph; it did not prove
   semantic inequivalence or compatibility. Later reconstruction audits were
   local Mac runs, with their own scope, not fresh Linux whole-cone evidence.
4. **New Port36 whole consumer:** reviewed `c0da01870c` Linux source has a fixed
   fresh stage, exact9080-core catalog, serialized project inputs, runtime ELF/
   alias closure, initializer/importer semantics, prospective and inside-scope
   admission and ownership monitoring. Its intended command is direct
   `.../bin/lean -j1 -M3200 -DElab.async=false
   /home/dombarker/Port36LINUX-367-20261025-v1/source/Port36LINUX_FullDriver.lean`.
   Entry **unconditionally refuses**, readiness false, runtime closure MISSING;
   no actual367 receipt. Calls364/365/366 were **Mac** failures: shadow/layout;
   initializer gate plus old killpg EPERM/lost metrics; optional region-array
   Inhabited/source error respectively. Monitor366 identity mismatch cause
   remains unknown. None is a failed Linux execution of this whole consumer.
5. **Separate privacy FinalNativeGate DATA setup:** v3 rejected ancestor0775
   before setup; v4 reported setup admission denied and published0664 receipts
   rejected by its reader. Exact denial reason is still unknown: follow-up
   reader observed14,107,502B above2MiB and read zero content. V5 transferred
   68 files/686,052B, transport78, guard ESRCH before setup Popen;
   `spawn_state=not_started`, admission unknown, no inside controls. Local caller
   additionally misclassified a defunct command and failed to retain its exit.
   Exact remote syscall/PID remains unknown. These are metadata/source/control
   bugs, **not Lean failures or completed final private Kani**.

All five comparisons use immutable receipts/source, not current live worker
state. Released strict SSH read-only query exit0 and v5's returned terminal
contradict a blanket network-unreachable explanation. No committed causal
evidence here attributes these failures to Mac ports, firewall or security
configuration changes. Source repairs do not themselves establish host readiness.

## Minimum next ordinary route, under existing policy

For an already-authorized focused theorem, the demonstrated route is one exact
absolute `lake env lean` command against a pinned warm job workspace, guarded
by full fresh admission under the shared lock and one independent 6G/8G/Swap0/
Tasks64 scope. Reuse the narrowly reviewed October24 command construction and
receipt capture where valid; do not recreate an entire launcher framework or
rely on the unprobed October19 path. Revalidate selected bytes, runtime and
dependency coherence, task attempt authority, complete populated reservations
below55GiB, and no unchanged-resource-failure retry. No command ran in this job.

For **the actual requested whole consumer**, a focused substitute cannot close
the target. The next concrete deliverable is the missing fixed Linux runtime/
ABI/serialized-input and source/control readiness evidence for the already
prepared367 caller, followed only upon lead allocation by that exact whole
consumer in the existing capped scope, with complete output/axioms/metrics.
Retain the current standard-core/importer/initializer checks and all security
boundaries. Success and feasibility below8GiB remain unestablished. Privacy's
final native setup/Kani59/60 remains a separate deliverable; it supplies no
soundness whole-consumer receipt.

## New versus reused validation; disposition

All Lean/host results above are **reused committed evidence**, with explicit
dirty-baseline, dependency/runtime, date and policy limitations. New validation
only checks immutable receipt/source hashes and axiom-log inclusion:
`validation.json`, exit0, 3.684105375s, self47,480,832B, max serial
child11,239,424B, swap counters0; aggregate peak unobserved. Its exact command,
collector SHA, source revision and219 input hashes are retained. The preceding
217-input validation is retained separately; the final run adds the two missing
historical driver provenance hashes and the complete5547 receipt, rather than
repeating an unchanged check. Two initial
collector failures are retained in `failed-collection.json`; neither was a
compiler/resource failure. An exploratory summary-display loop also ended with
AttributeError after printing the relevant metrics because it treated a string
summary as a row; no evidence or claimed result depended on that loop.

No formal assumptions discharged, added, weakened, or hidden. No shipped source,
launcher implementation, protocol, wire, feature, key, security contract or
frozen pin changed. Both deployed security targets remain **NOT ESTABLISHED**.
No merge/push; stop for lead review with the exact readiness gaps above.
