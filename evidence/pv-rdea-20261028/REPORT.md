# LOG D399 resumed: reachable requests and endpoint consumers

**V181 SUSPENDED; V178 SUSPENDED. No checked privacy finding; no row restored.**
The remaining blockers are concrete simulation and reachability/public-provenance
certificates described below. Allocation failure on a public-sized request is
**not** a blocker. This continuation supersedes the original report's contrary
stopping conclusion and unconditional native-success interpretation.

Exact worktree `/Users/dominic/ZK/.worktrees/pv-rdea`, unchanged branch
`codex/pv-rdea-20261028`; resumed source head `713a92729abc0bb55677dd2ea7d2107490b5cd24`.
No changes under crates/ or programs/, no dictionary, simulator, observer, key,
launcher, shared environment, or shared library edits; no push. T remains exactly
`entropy_law`, `entropy_kernel`, `observation`. No headline premise is removed.

## Ruling rdea-1 and before/after statements

The retained item **runtime/allocator primitive adequacy** covers whether a
public-sized allocation succeeds, including allocator state left by earlier
witness-dependent execution. It also covers the failure-selected termination
prefix of the planned public request word. No new trust item or allocator-state
equality premise was introduced. Full outcomes, addresses, errors, memory,
frames and histories remain in the physical execution; the size-word projection
is an auxiliary proof, not a replacement observer.

**V181 before:** `op30(n) = ok empty` for every Usize was the old value-only
reference, with native/world correspondence residual. Its unconditional native
success interpretation is superseded.

**V181 after:** native `with_capacity(n)` equals `String::new; reserve_exact(n)`
with complete Result, buffer and post-world. The consumer explicitly branches:
`error e => failure e postWorld`; `ok () => next buffer postWorld`.
At the actual literal 69, exactly one request `(0,69,1)` occurs, even if it fails.
After success, the 64 ordered one-byte digit appends and five-byte suffix append
fit the existing capacity and issue no more allocations. The digest's contents
are unrestricted; length 32 is derived from the extracted array type.
See `PV_RDEA_V181ConsumedLaw`, `ReservationExecution`, `NameFill`, and
[rows/V181.json](rows/V181.json).

**V178 before:** successful contents used a fresh-output reference; native
clone-first allocation/world effects were residual.

**V178 after:** concrete clone, optional clear, optional separator append and
final append preserve the error/post-world consumer. Success consumes the old
contents formula in the actual world. Every failure ends at a prefix of the
planned request-size/order word. That word depends on lengths, capacities and
Unix path predicates, not byte contents. The four literal argument lengths and
relative branches are derived from the source spellings. Hex basename length
69 and absence of slash hold even for a secret digest of length 32.
See `PV_RDEA_V178ConsumedLaw`, `JoinRequests`, `JoinSuccessRequests`,
`LiteralSites`, `ReservationJoin`, and [rows/V178.json](rows/V178.json).

## Mechanical deployed inventory

A capped Linux release build selected `devnet_spend`,
`r1p-check,aspis-r1-cost-probe/ct-host-prover`, locked dependencies and rustc
1.94.1 (`e408947bfd200af42db322daf0fadfe7e26d3bd1`, LLVM21.1.8).
The binary SHA256 is
`fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`.
A subsequent root-only save-temps emission produced exactly the same binary.
The inherited 487-unit feature graph is retained and hashed. Workspace source
pins and the host source identity check are in `build-source-pins.json` and
`build-source-check.json`; source code was not modified for diagnostics.

The evidence includes optimized LLVM IR, source-spanned MIR, ELF relocation/GOT
resolution, pre-optimization root bitcode converted to IR, and installed exact
std/alloc bitcode with compiler inline-debug chains. MIR emission alone was
omitted for libsecp256k1 after generated-table emission stalled; its LLVM IR
remained emitted and its source target-method scan is retained. No missing MIR
for this arithmetic crate is treated as a formal completeness certificate.

`site-reconciliation.json` records **37 MIR candidate functions / 54 source
sites**, each with exact source span, argument-producing excerpt, source hash
and body hash, plus **15 stdlib inline contexts** with full caller chains.
`runtime-unit-closure.json` mechanically excludes build-script/proc-macro-only
units. Those exclusions are stronger than absence of an out-of-line symbol.

The linked machine image contains exactly five resolved direct/GOT calls into
`Path::_join`: four in `plan::prove` (note-recovery.json, mask-nonce-ledger,
proof.bin, statement.bin) and one in durable-store `reserve_fallible` (the
32-byte-digest hexadecimal name). The model inventory originally covered only
one op26 and one op30 occurrence; the new inventory explicitly reconciles that
narrow model with the four additional client literals and runtime diagnostics.

Additional stdlib constructors: `format_inner` uses template-only
`estimated_capacity`; `from_utf8_lossy` uses input byte length after an invalid
UTF-8 guard; `locate_build_id` uses `23+6+2*build_id.len()+1` after public-metadata
and filesystem guards. Linked lossy callers are OS error Debug/Display and three
addr2line file-rendering calls. Backtrace pushes include debuglink, debugaltlink
and split-DWARF paths, with exact origin chains and argument excerpts retained.
The fmt hex-template initial capacity is proved zero at the decoded-template
model boundary; this does not certify the native template-parser bridge.

**Exhaustive reachable-call certification remains incomplete.** The corrected
LLVM graph has 79,569 definitions, 3,315 direct-graph reachable symbols and 1,041
unresolved indirect instructions. Unit-local symbols are qualified by LLVM
module. The ELF graph resolves 2,254 relative relocations and 1,054 reachable
functions, but register callbacks remain. Runtime candidates such as anyhow
ensure formatting, pow::hex, generic itertools joins and num_cpus are explicitly
marked unresolved/excluded-from-the-resolved-linked-set, never declared
unreachable merely because `nm` lacks their original function symbol. The
machine/inline inventories are conservative candidate evidence, not a silently
promoted exact reachable set. Initial unqualified/comment-scanning graph results
are retained as uncredited diagnostics and superseded by the corrected graph.

## Actual source consumer connection and exact blockers

A private coherent 27-module source replay compiled the exact FullTypes,
FullFuns and capacity/append adapter cone. A named symbolic factorization proves
that the **actual extracted** `reservation_path` equals its unchanged SHA prelude
followed by its constructor/name/join tail. The actual tail calls op30 at 69;
its failure stops before the name/join consumer. The actual name loop equals 32
finite rounds by induction; no SHA evaluation or concrete recurrence replay was
used. The exact 16-entry source table and successful lookup's one-byte length
are proved. These are source execution theorems, not only arbitrary-continuation
congruence lemmas.

The remaining V181 blocker is the representation-and-world simulation between
that extracted `Result String` callback ABI and the physical Buffer/World
constructor plus actual op31 appends and native handlers. The byte-fill theorem
is not yet identified with all operations of the extracted finite round.
The remaining V178 blocker is the analogous actual op26 consumer simulation,
including owned String destruction and native unwind/error handlers. The
physical clone/append consumer itself is concrete and proved.

Both rows also lack a completed native dispatch closure and source-derived
public-environment/header certificate for every diagnostic invocation guard,
argument and request. No witness-dependent size/order counterexample was found;
absence of such a counterexample is not a proof of public provenance.
Allocation-failure noninterference and prior witness-dependent allocator state
are reported under **runtime/allocator primitive adequacy**, not as additional
blocking obligations. E1/E2, RunJoin, client route, native compiler/runtime
correspondence and L1/L2/L3 remain retained/residual. The headline target is not
established.

## Verification, resources and operational record

All **100 Lean attempts** were used: **70 successful, 30 failed**; **19 native
scopes conservatively charged**, zero Kani. Peak Lean RSS **3,289,144 KiB**,
all recorded swaps zero. The 96-attempt continuation budget is exhausted.
Final attempt and native receipt indexes are generated in `attempts.json` and
`native-scopes.json`: exact target, exit status, wall time, peak RSS, swap,
source revision/blob/SHA, command/caps and every `#print axioms` line. Failed
elaborations' `sorryAx` output is explicitly uncredited. Final accepted theorems
use only propext, Classical.choice and Quot.sound (or subsets/no axioms).
The combined physical statement/axioms audit uses ID60398; ID60399 is the
focused actual-source replay. These are distinct source targets and coherent
object cohorts. Neither falsely asserts the missing cross-cohort/native bridge.
No unchanged full regression, package-wide build, Kani run or heartbeat/depth
increase was used. Inherited native fixture results are identified as inherited;
this run's denied-allocation fixture is not evidence of witness dependence.

All compiler/native scopes used High6G, Max8G, SwapMax0, TasksMax64; Lean -M7000.
The cold dependency cone was only 27 pinned modules, one module per scope.
Build02 failed lld thread creation; Build03 was stopped after generated-table
MIR review. CPU affinity and reduced MIR emission repaired the diagnostic build;
Build04-retry passed. No memory kill was retried with a higher cap. Scope04's
internal admission race refused before compilation and consumed no Lean ID.

Operational exceptions are not hidden: ID60309 was incorrectly launched after
an `allowed:false` outer admission result; this was disclosed during work and
is not an operationally compliant run, though its theorem was subsequently
consumed by the final audits under valid caps/admission. Two read-only admission
snapshots were taken a few seconds before the full 180-second retry cooldown;
the corresponding later compilers launched after the cooldown. Early resumed
admission stdout was captured by the tool but not always also redirected to a
host .log; JSON snapshots remain. Later launches preserve both host JSON/log and
require allowed:true **and** exit0. IDs60340–42 failed before useful elaboration
while setting up only this job's copied environment/cache; the private prefix
was fixed under the owned-input exception, with no shared infrastructure edits.
ID60388 prematurely attempted a dependent lookup module before its table object
existed; it failed at import and is counted, with no proof credit.
ID60340 has no launcher SHA file; its source revision/hash is recovered from
the unchanged private source authority/preflight, and its import failure is
explicitly uncredited. ID60390 hit the default recursion limit in a one-byte conversion simplifier;
it was replaced by a named two-step symbolic lemma, with no limit raised.
ID60394 had two admission refusals, consuming no attempt; its successful
21:58:32 retry retained the same ID and waited over 180 seconds after each
refusal (21:52:06 and 21:55:29). All failures remain in the receipt ledger.

## Next concrete deliverable

Produce a concrete simulation theorem from
`PV_RDEA_ActualEndpointConsumer.afterCapacity` and the actual op26 tail into the
physical `V181ConsumedLaw`/`V178ConsumedLaw`, retaining error handlers, frames and
owned-argument cleanup. In parallel as a separate deliverable, close native
indirect reachability and classify every diagnostic argument/guard/header from
public source data. Then replay the resulting endpoint instance. The current
local row laws and source factorization are reusable predecessors, not a claim
that this final deliverable is already proved.

## Final audit receipts and artifact retention

| ID | Exact target | Exit | Wall | Peak RSS KiB | Swaps | Exact source revision |
|---|---|---:|---|---:|---:|---|
| 60395 | `R1Z.PV_RDEA_V181ConsumedLaw` | 0 | 0:02.63 | 2623428 | 0 | `7bee4be4db198b1f7dfed25cbaa3a674d4f172d8` |
| 60396 | `R1Z.PV_RDEA_V178ConsumedLaw` | 0 | 0:01.36 | 2625364 | 0 | `893df939592f246b4cc35b158736cc38dcd773ed` |
| 60398 | `R1Z.PV_RDEA_CombinedStatements` | 0 | 0:01.19 | 2627452 | 0 | `6245678956d2ef4e5eb759f39e4dc34bd71d1656` |
| 60399 | `R1Z.PV_RDEA_FocusedReplay` | 0 | 0:01.60 | 2636128 | 0 | `6245678956d2ef4e5eb759f39e4dc34bd71d1656` |

Each target's full statement/axiom output is in `out-ID.log`; the exact commands,
source blobs and SHA256s are in `attempts.json`. Native exact source revision
for the deployed build is the resumed 713a92729a revision; full feature/profile
selection is inherited and hash-pinned in the 487-unit graph. Additional root
manifest/lock hashes match that revision. The host snapshot omits only the
tracked `.cargo/config.toml` containing the unused xtask alias; this is recorded
in `additional-build-inputs-check.json`, not represented as byte-identical config.

`COMMITS.txt` records `git log --oneline 3e77ed7b62..HEAD` through the final proof
and row-status commits; the final evidence-only commits follow that snapshot.
No local target directory exists. Compiler objects and Rust targets remain only
in the owned Linux build-host cache for the next pinned dependent proof; their
hashes are retained and no binary/.olean/.bc payload is committed. Compressed
IR and every committed evidence file are below 20 MB. No wallet/account keys
were created, removed or used.
