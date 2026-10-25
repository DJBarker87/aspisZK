# Repair status at f56 continuation

This revision supersedes the runtime/hash/cache/cleanup readiness descriptions
below. See FinalNativeGate-SETUP-PROPOSAL.md for the concrete source and remaining
interfaces. Public entries remain unconditionally disabled. No host data read.
The new finite catalog/FD reader and independent cleanup are source repairs;
fixed-scope shutdown is still unimplemented and every spawned scope is reported
UNRESOLVED. No successful receipt can be inferred from wrapper exit. Setup source
exists but is partial, unallocated and UNREADY. Cache choice is null; optimized
dev opt-level3 is restored in the proposal. Historical sections follow as design
context, not claims that these interfaces are complete or accepted.

# FinalNativeGate prospective fixed producer (SOURCE ONLY)

Criteria were committed first at4008aeadf2. Base dcc848acfc3c5c9dd95003a7ea0bcff5d924b59b.
All code belongs to this parked unmerged candidate. No shipped source, model,
protocol, wire, feature, trust or security-contract changes. Public main in BOTH
FinalNativeGate.py and FinalNativeGate_inside.py returns78 unconditionally.
No argument, metadata flag, environment value or global can activate either.
Private bodies are reviewable source, exercised only through explicit mocks.

## Actual entry flow represented by the source

Future prospective main -> fixed staging path and exclusive0700 packet -> sealed
source plan -> inherited limits -> London lock outside22:30–14:00 -> persistent
owned-lineage watchdog -> pre source/tool/runtime/cache/env pins -> concrete
collect(prospective), Q4GiB -> ONE fixed systemd user scope -> fixed inside entry.
Inside body -> same pinned runtime/limits -> persistent watchdog -> pre pins ->
actual self cgroup controls -> full collect(inside-scope), Q0 -> full collect(go),
again inside-scope Q0 -> self PID/starttime/control binding -> GO pins equality ->
open exclusive raw captures -> durable exclusive charge59->60 -> ONE Popen of
literal COMMAND -> wait4/control checks -> raw logs fsync -> post source/tool/
runtime pins, post cache inventory, final controls -> guard/terminal receipts.
A zero command exit still says pending proof review, never full native closure.

Each collect executes the existing full visibility collector and BOTH bound
hierarchy scans followed by the unchanged evaluate body. No fresh_admission
argument, GO callback, supplied policy projection or caller command is accepted.
Adapter changes only import namespace and expected fixed scope unit. Collector
changes only map the unique raw-capture label go to policy phase inside-scope.
That prevents exclusive inside raw receipts from being overwritten by GO.

Own4GiB is reserved in the existing finite frontier and additional Q=0 inside;
fixtures assert projected4GiB, never8GiB. Prospective adds4GiB to its actual
frontier. Unchanged policy enforces strict populated frontier<55GiB;
raw MemAvailable minus active_file, KReclaimable, floor(SReclaimable/2), and FULL
root residual must exceed projected reservations+7GiB; raw available must also
exceed Q+2GiB. Visibility errors/unbounded groups/identity/control races deny.
All raw snapshots, visibility commands, errors and decisions remain captured.
ResourceMeta1G epoch7 is historical metadata only, neither4GiB admission nor
API adoption. No SbfProducer20a helper, mount, namespace, sudo or rootfs is
required for this ordinary user Kani source. No SBF restriction was bypassed.

## Exact command, directories and preparation boundary

Fixed new launcher staging directory:
/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate
Fresh one-shot child packet: FinalNativeGate-packet (never overwritten/reused).
Superseded empty-cache proposal (not selected): FinalNativeGate-target, same stage. Preparation of its
empty directory is a separately allocated setup action, NOT done in this job.
The command uses the existing scalar proof/package paths, no harness changes:

```
/usr/bin/timeout 240 /home/dombarker/.cargo/bin/cargo kani --manifest-path /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-scalar/proof/Cargo.toml --lib --exact --harness checks::paired_coordinate_native_resume --solver kissat --output-format terse -j 1 -Z unstable-options -Z stubbing --extra-pointer-checks --cbmc-args --unwinding-assertions
```

Separated -j 1 and -Z spellings match FINAL-SLOT. Harness unwind66 is unchanged;
no new compiler preflight, observer, stub, quantifier, scan/copy/wipe/cfg, solver,
timeout or cap change. Proposed fixed environment retains the scalar cfg and
codegenunits1; offline buildjobs1, no inherited arbitrary flags. It remains a
PROPOSAL with unknown user bus/rlimits recorded, not accepted environment data.
Time is expected in frontend/compilation, then ONE paired symbolic CBMC/kissat
step. Ordinary optimized MIR compilation is not Kani harness typechecking.
No separate typecheck is allocated; parse/typecheck failures consume the final
slot once Popen is attempted. Last Rust slot remains reserved and unspent.

## Pin plan and remaining concrete interface

FinalNativeGate-source-map.json shows exact dcc scalar source bytes versus the
historical MIR host paths and hashes. Plan retains package file hashes from
historical unchanged MIR copies, tool/registry hashes and current local proof
bytes. Host scalar freshness is NOT observed. The historical50077 fingerprint
63746246066065c3885fbdb48de006d5bf5dec11c7c9d6fe8a70c541327d7ded belongs only to
ac5614d248's ordinary1GiB MIR build (5.72s, exit0); no retrospective4GiB gate.
Large old inventories are retained by hash+size only. No host universe was
hashed or queried from this Mac.

_plan fails explicitly while ANY host_runtime, native_runtime_dependencies,
cache_inventory, environment or inherited_limits value is null. They ARE null.
Before execution the lead needs one separately allocated bounded metadata/setup
packet supplying exact Python executable/stdlib/mapped libraries and tools,
Kani/cargo-kani/compiler/sysroot/CBMC/kissat/native runtime closure, fixed cache,
env and inherited limit pins. Listing tool roots alone is insufficient: assess
native dynamic-loader/library dependencies and child tools, then add fixed roots
and exact hashes to the sealed plan. _pins reads those roots directly, compares
all files; no metadata GO value authorizes an execution. The prospective stage
has not been uploaded or observed. Fresh actual identities/controls/admission
are runtime observations, not prefilled assumptions. No full stale inventory
can be used as a runtime authority substitute.

All job module bytes except the one-line bootstrap seal are in plan.files.
The plan hash lives in FinalNativeGate_seal.py, whose exact source spelling is
checked. Lead must independently pin that bootstrap file using reviewed Git and
transfer receipt. This avoids circular self-hashing. Existing OS/Python/import/
compiler/Kani/trusted-policy boundaries remain; file hashes do NOT prove which
body executed or a Rust/LLVM semantic theorem. The reused runtime_pins function
records env ELF ABI/interpreter/DT_NEEDED, Python stdlib/mapped libraries/tools;
it does not claim a complete native Kani dependency closure. Missing closure
pins are an exact next deliverable, unrelated to the SBF root-helper interface.

Fresh pre/GO pins include cache; post permits legitimate Cargo output changes,
records the post cache, and still requires source/native/runtime equality. No
source upload or mutation is allowed between pre and GO. This is snapshot
freshness with a sampled monitor, not an atomic filesystem or continuous-memory
proof; final actual runtime review must assess that operational boundary.

## Durable charge, guard and lifecycle

Charge receipt is exclusive mode x, file flush+fsync then directory fsync, before
Popen. If any admission/pin/control/capture-open fails first: zero Kani charge.
Once charge creation starts, uncertainty is conservatively consumed; frontend,
parse, resource, solver and spawn failures cannot reclaim the slot. Packet and
charge are never erased. No rerun path, numeric PID kill or arbitrary job API.
Only the actual direct child's pidfd is signalled after PID/starttime/parent
checks; guard cancellation uses previously observed owned lineage and stable
pidfds. Reap/capture errors stay failed with null unobserved metrics. Parent and
inside monitors retain sampled lineage, errors, cancellations and resource data.
Fixed cgroup3GHigh/4GMax/Swap0/Tasks64 is authoritative; any high/max/OOM event
fails. Guard is a bounded sampler, not a theorem against all short-lived peaks.
The new job guard uses4GiB (not the metadata watchdog512MiB) because it includes
the actual4GiB workload; sample budget32768 covers the fixed lifecycle. No actual
metadata/guard/native process was launched here. Local fixtures stayed<512MiB.

Raw child stdout/stderr and scope stdout/stderr are distinct. wait4 preserves
actual exit/rusage; controls preserve memory.peak/current/swap/events/task counts;
full raw admission/ordered reads preserve freshness errors. If packet fsync or
terminal capture fails, no successful receipt exists; the exclusive charge still
blocks retry. Outer lifecycle ceilings are cancellation deadlines only, never
an increase to the literal240-second solver timeout. Runtime lifecycle has not
been validated on Linux; mock results do not certify kernel/pidfd/systemd
semantics or rootless child shutdown under all schedules.

Finite receipt families: pre/GO/post pins; prospective/inside/GO ordered raw reads,
reports and metrics; controls pre/GO/post; charge and actual child identity/argv;
raw logs; wait status/rusage; guard lineage/cancellations; parent lock/scope exit;
terminal with actual code/charged/spawned/errors and missing metrics as null.
No labels assert runtime/full admission/security closure. DerivedJSON>5MB stays
external with size/hash only; no objects/binaries/ELFs enter Git.

## Validation scope, statements and retained gaps

No theorem/premise statement changed: BEFORE=AFTER scalar RELATION and P6
SOURCE-CONTRACT, including complete arbitrary nonce32/postbuffer64, entry16,
Ok/Err valid NonZeroI32, sole coordinate j, unchanged real scans/copies/wipes,
return-control/error/live fields and separate disposal. Ghost ledger remains
bookkeeping, not OSWorld. Observation subgraph reduction is not a whole-formula
or solver-performance guarantee. Old059240s timeout and all failed fixture
approaches remain retained. Only four tiny original raw policy generators are
reused; new integration tests do not rerun the whole unchanged policy suite.

No assumed sourceDrop=dropSpec premise is supplied. BuilderDropObservation's
P6Route.specification still demands that equality for every memory; heap frame
lemmas do not produce current typed-reborrow/Copy/static-store native instance.
NativeTypes/ErasureFns callbacks, alias/value constructors, generic moveSwap,
coordinate/capacity Nat facts and049/050 component checks do not fill it. MIR
cfg excludes Kani and its error constructor. Current paired harness remains
UNRUN/uncompiled as Kani. This step supplies reviewable execution-preparation
source, no new native semantic result. Native Drop/whole-model/world/E1/
controller/reachability/rank/finite16/outer8/full transcript/L1/L2/L3/client/
adoption/performance/artifact gaps all remain. Both security targets NOT
ESTABLISHED. No new trust assumptions or discharged semantic premises.

Lean240/260; Kani59/60 FINAL1 RESERVED; Rust2/3 conservative charges, actual
ordinary build1 carried; extraction54/56; backend15/16; ELF0/3 unchanged. ZERO
actual host/SSH/network/compiler/parser/typecheck/solver/Rust/Cargo/Kani/Lean/
extraction/backend/ELF/native-body/probe/root/sudo/ns actions in this step.
Python AST inspection below concerns Python text only, never a native parser.
No wallet keys read/created/copied/deleted, no RPC, no merge/push.
