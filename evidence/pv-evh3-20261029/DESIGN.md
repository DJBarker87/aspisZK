# PV_EVH event producer: pre-registered design and acceptance gate

Written before any new Lean. Baseline: `946718387da2351a46a3a095a94f1f003d5f8185`,
branch `codex/pv-evh-20261029`, sparse worktree `/Users/dominic/ZK/.worktrees/pv-evh`.
Receipt root: `evidence/pv-evh3-20261029/`. Only new `PV_EVH_` modules are permitted.
Budget ceiling: 80 Lean, zero native, zero Kani; env-J 73000–73099, audits 73097–73099.
Existing host workspace is `codex-pv-evh-20261029`; no new cache cohort is proposed.

## Acceptance criteria (registered before implementation)

(a) The producer must execute the EXISTING extraction of the deployed client and
prover entry, not a handwritten client, handler callback, supplied trace, or
post-hoc Result decoder. Exact existing extracted library entry:
`ProverRwFull.RealR1_client.prove_for_proof_accounts`, crate
`aspis-r1-cost-probe`, source `crates/aspis-r1-cost-probe/src/RealR1_client.rs`.
Its extraction is tracked at
`docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean`.
The nested prover entries are `prover.prove_masked_retrying_with`,
`prover.prove_masked_attempt`, and `prover.prove_masked_with_attempt`.
All paths in this design refer to the exact baseline revision above; this is a
source snapshot pin, not a claim of a fresh generation receipt or feature parity.
The actual executable is `devnet_spend`, package `aspis-r1-cu-probe`,
`tools/r1-cost-probe`, with `r1p-check,aspis-r1-cost-probe/ct-host-prover`, release,
Rust 1.94.1. Its entry is `main`, dispatching to `plan::run` and `plan::prove`.
We must locate a provenance-pinned extraction of these executable entries before
claiming a deployed-client producer. A library entry alone does not satisfy (a).

(b) Exhaustively inventory the selected extraction's `ExternalFuns`: record
EVERY op, full type, alias, and textual extracted call sites. Classify file,
stdout/stderr, clock, getrandom, network/RPC, allocation failure, panic/abort/exit.
Do not infer an absent effect is absent from native execution. Missing executable
coverage is an explicit gap. Pin source call sites in the Rust executable as
well. Candidate mappings use EXISTING constructors only:

| Effect | Event constructor / required data |
| --- | --- |
| proof / statement write | `proofWrite` / `statementWrite`: path, requested and delivered bytes |
| other filesystem effects, including partial/error paths | `otherFile`: exact existing `FileOp` payload |
| returned JSON / stdout | `returned` / `printed`: actual bytes; requests and deliveries for stdout |
| stderr, formatting, panic, abort, exit | `diag2` / `diag3`: exact existing effect payload; matching terminal |
| entropy | `side` with explicit operation tag and visible metadata; private seed bytes must not be exposed by invention |
| attempts / rejection | `count` / `rejection`: exact entered/rejected order |
| serialized wall time | `wall`; physical timing and scheduling remain retained D159 obligations |
| ROM queries | `oracle`: address and answer, ordered with duplicates and rejected prefixes |
| RPC/network and allocator/runtime effects | `side`: named visible operation payload; no unsupported projection to silence |

This is a mapping specification, NOT an implemented interpretation. Payload
availability must be checked for each operation. Mapping only the final Result
or supplying a whole helper trace as an arbitrary answer fails (b).

(c) `nativeEvents := run(extracted entry)` in an event-writer world. Each
primitive appends the actual event before returning its world's answer and
updated world. Bind appends ordered prefixes on success, and preserves the
entire prefix on failure, panic, abort, exit, and every finite divergent prefix.
Fuel exhaustion must be distinguished from actual divergence. Pure helpers
cannot conceal effectful callees. Existing `PV_W_Threading.bind` has appropriate
prefix retention, but its existence does not supply the executable syntax.

(d) The OS/runtime boundary is the world's actual responses, delivered bytes,
allocation results, scheduling, and physical/serialized timing. Entropy laws map
to existing `PV_RunJoin_TrustItems.entropy_law` / `entropy_kernel`; native/world
observation adequacy maps to its existing `observation`. Source/compiled-code
preservation remains V370, CPU latency V371, allocation/error/abort rdea-1,
Option-B failure independence V400, client pin V396 and complete transcript
association D159/D166 and existing L1/L2/L3 obligations. Deterministic writer
semantics and source association are P work, not additions to T. No T field may
be introduced, and missing source coverage must not be renamed OS trust.

(e) Intended OPEN data selections to DEFINE, conditional on (a)–(d): `native`,
`fileTrace`, `jsonStdout`, `errorStderr`, `countTrace`, `timeTrace`, `oraclePrefix`.
Every projection must use the UNCHANGED `PV_RJ4IDB.nativeFiles`, `nativeJSON`,
`nativeStdout`, `nativeDiag2`, `nativeDiag3`, `nativeCounts`, `nativeRejections`,
`nativeTimes`, `nativeOracle`. The remaining twelve OPEN fields stay open:
completion, publicInput, acquisition, signal, toNative, toModel, statementBytes,
retained, actualProgram, terminal, semantic, point. Invocation/store/ops
installation obligations remain explicit. Definitions alone do not close the
corresponding privacy laws.

(f) Ruling (v): prove a joint witness of ALL claimed links together with the
existing `NativePublication55.actual/published` binding. Prefer a deployed path;
otherwise label the witness MODEL WORLD. Independently choosing empty traces
and an unrelated publication does not witness source-associated links. No new
skeleton earns credit without this proof.

## Initial preflight finding and stop condition

The tracked extraction describes the library entry, with fixed `ExternalFuns`
returning `Aeneas.Std.Result`, without writer/world state. The executable's
`main`, `plan::prove`, recovery/proof/statement writes, JSON, stdout and outer
clock are not supplied by that extraction. Existing `PV_W_ProverEntry` wraps
`prove_masked_with_attempt` as a helper thunk; existing `PV_DIAG3` client
handlers are parameters, not an extraction of executable main.

Before writing any Lean, mechanically check these facts, all op signatures,
and the current Rust call sites. If confirmed, (a) and (b) FAIL: do not implement
a model writer and label it the requested producer. Report the exact missing
entries and the existing source-level entropy obstruction. This is a source
coverage/interface blocker, not a memory, cohort, finite-carrier, or T change.
No changed extraction/compiler/native execution is available under the stated
zero native budget. No additional permission is inferred.

## D474(C) re-extraction boundary

Pin this baseline even while pv-c474 drafts diagnostics. A future exact
executable extraction must separate the executable diagnostic/reporting call
cone from the prover effect interface. D474 changes then replace the pinned
client diagnostic syntax and its call-site map locally, followed by fresh
source/feature hashes, projection proofs, joint witness, and affected replay.
Do not anticipate or adopt the draft source. Names of rows removed at design
stage: NONE. Acceptance failure must retain all 19 OPEN selections and all
existing privacy premises, with no added trust or weakened observer/simulator.
