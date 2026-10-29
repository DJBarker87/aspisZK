# Direct executable extraction: Charon candidate retained; Aeneas blocked

Branch `codex/pv-cx-20261029`, baseline
`27b582ca44a9ef7c1fc341fb9bc58610d28ed7f1`. The requested Lean extraction,
compiled prover link, and completed ExternalFuns interface are **not delivered**.
No privacy premise is discharged; the target is not yet established.

## Delivered source extraction

N73309 runs the unchanged retained Charon 0.1.223 on the actual frozen
`tools/r1-cost-probe` package's `devnet_spend` binary. No port/reference crate,
source rewrite, dependency substitution, or prover duplication is used.
`main`, `plan::run`, and `plan::prove` all have Structured bodies. All 1,225
staged input files byte-match baseline git objects. The LLBC's embedded main,
plan and Client64_accounts source contents independently match those inputs.
See `frozen-source-pins.json`, `checks.json`, and `artifact-manifest.json`.

The retained final text artifact is `archives/N73309.llbc.xz`; uncompressed
SHA-256 `db06ad45e0ca51cd260e2c420165c7c7d66f0bd4c12d816de8f9f3c98a982e74`,
46,737,953 bytes. It has `has_errors=false` and no extraction warnings.
Rust dependency compilation warnings are retained separately in the run log.
The compressed rejected N73305 artifact preserves the earlier failure.

Historical flags start with preset aeneas, MIR built, sysroot default. Final
permitted flag adaptations: `--monomorphize`; include only the data declarations
ControlFlow, Option, Result and PoolV1PairForestTerminalPaymentV1; keep their
children opaque with `Type::_` markings. The complete exact command/options
are in N73309/command.json and artifact-manifest.json. Root includes `crate`,
all other names default opaque. No `--no-typecheck`, skipped borrow checking,
or unchecked transformed-type result is accepted.

The opacity audit found compiler-generated destruction bodies as well as
ordinary Rust functions. N73309 makes enum child glue opaque; 13 nonlocal
array/slice/ptr drop-glue bodies remain explicitly inventoried in
`synthesized-glue.json` and `effect-interface.json`. Their effect/termination
adequacy is NOT proved. Do not claim a complete runtime effect extraction or
that every compiler primitive has become an ExternalFuns field.

## Failure isolation and exact tool blocker

N73300/1/3 failed on my incomplete archive staging; exact missing paths and
changed inputs are in pre-extraction-failures.md. N73302's linker exhausted
TasksMax=64. Four-CPU affinity and the historical four-thread linker flag fixed
that without raising caps. The same private Cargo cache was reused throughout.

N73304/5 exited 0 but their LLBC has_errors flag is true: Charon reports a
transformed trait-clause mismatch at `/rustc/library/core/src/iter/adapters/enumerate.rs:62:1`:
expected `Enumerate<I>: Iterator<&'a T>`, got `Iterator<Enumerate<I>, (usize, Clause0_Item)>`.
The source loop is Client64_accounts.rs:18–25. No-normalize did not fix it.
Monomorphization removed that diagnostic; N73306/7 still had opaque enum
reads (thus has_errors=true). N73308/9 include the necessary enum data and
have has_errors=false. No source adaptation was shown necessary.

The historical ProverRwFull chain is caller-005 followed by tracked
`tools/prover-rw-20261023/stage3/adapt-caller.py`. Its pinned Aeneas binary is
4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5
(49,419,624 bytes), b59d5188 extended. The recorded host executable path is
absent. The readily available 562e1f51… backup has nine OCaml source differences
among 101 checked source files against the historical manifest. It is a
version split, not merely a build-instance difference, and was NOT substituted.
See inherited-tool-binary-pins.json, historical-aeneas-source-manifest.json,
aeneas-backup-comparison.json and tool-status.md. Bounded backup searches
found no exact candidate; the deeper 25-second search timed out, so no claim
of an exhaustive whole-host search is made. The exact-backup question was
raised asynchronously while Charon work continued; no answer was received.

This stops Aeneas/Lean under local-lean rule 5 (do not repair tool infrastructure),
not because a deployed body requires rewriting, and not because the budget is
exhausted. No Aeneas invocation, Types/Funs generation, Lean elaboration, axioms
audit, or manifest replay is claimed. The rule against changing/substituting
extractors is retained.

## Boundary, interface and future release

The new call to the EXISTING prover is opaque function 310, with its exact
monomorphized Rust signature and one call site, plan.rs:116:12–133.
`prover-boundary.json` records it; `existing-prover-signature.txt` records the
Lean target `ProverRwFull.RealR1_client.prove_for_proof_accounts`.
RealR1_client.rs SHA 55ceff43… equals caller-005's source binding. This locates
the Rust boundary and avoids duplicating the prover. It is NOT a compiled
Lean carrier/type-identity link; that remains the next step after Aeneas.

`effect-interface.json` enumerates ALL 436 opaque functions in N73309, their
structured Rust names/signatures/generics, definition spans and 1,146 distinct
static call/drop sites. It also inventories 71 local bodies, nonexternal
terminals and the 13 remaining nonlocal glue bodies. This is a Charon inventory,
NOT an emitted ExternalFuns class. Coarse file/stdout/stderr/JSON/clock/entropy/
exit/alloc/library categories are candidates, not effect-freedom laws; 62
operations are explicitly unclassified. Full transitive classification and
allocation/panic/unwind/drop adequacy remain open. The requested complete,
compiled effect interface is therefore not claimed.

Extraction uses nightly-2026-06-01 (rustc 1.98.0-nightly 14210df0e), release
opt-level 3, debug assertions and overflow checks off, locked/offline baseline
Cargo resolution, features r1p-check and aspis-r1-cost-probe/ct-host-prover.
`resolved-features.json` lists every resolved crate/version/feature set. This
retains the x' boundary to deployed 1.94.1 and V370. No source-level law for an
opaque dependency is inferred, and the compiler-generated glue is not silently
identified with a 1.94.1 runtime implementation.

`D474-spans.json` gives exact old/new hunks for committed diagnostic draft
0046a7446d5519d1feb51ac502e2f7962038fac1. Its parent main, plan, accounts and
manifest byte-equal this baseline. The main diagnostic routing, plan error/
reporting/time serialization, account diagnostics and client profile/build
recipe are localized there; the new diagnostics module is explicitly listed.
This draft is not the final owner-approved bundled release: insecure-fixture
disablement, constant-time private-input decoding and N7 custody may touch
additional spans. Recompute this map on that final bundle; no draft is adopted.

The next EVH world MUST BE STATEFUL. The existing
R1Z.ProverRwEntropyIteration.no_retry_then_success rules out a fixed pure
entropy dictionary for reject-zero then successful retry. No writer world,
new observer, weakened simulator, extra trust item or skeleton theorem was made.
Before/after: same 19 OPEN runtime fields; zero ledger rows/premises removed,
added, reclassified or changed. V370/V371, rdea-1, V400/V396, D159/D166 and the
existing L1/L2/L3/source/experiment obligations remain retained.

## Validation and handoff

Usage: 10/30 native scopes (N73300–N73309), all Charon; 0 Aeneas, 0/60 Lean,
0 Kani. N73306 had one unlaunched admission refusal (not charged), followed by
more than 180 seconds of cooldown and a compliant retry under the SAME ID.
Both admission signals were checked immediately before every actual launch;
all actual scopes have a positive admission and the exact 6G/8G/swap-0/64 caps.
Every receipt records command, source revision, wall, GNU-time RSS, cgroup peak,
swap and N/A print-axioms status. No source failure was retried unchanged:
staging or extractor flags changed in each retry. No Lean launcher was written,
so the failed-Lean-source guard was not exercised.

Final N73309: exit 0, 3.590 seconds, GNU-time RSS 548,216 KiB, cgroup peak
614,440,960 bytes, zero swap. Largest completed scope: N73304, 2,693,529,600-byte
cgroup peak, zero swap. No memory kill or ten-minute-without-target review point
occurred. verify.py checks every staged source hash against baseline git; the
compressed archives were decompressed and independently SHA-checked. Python
scripts parse; all frozen crates/programs/tools/r1-cost-probe paths are unchanged.
No generated Lean, project/library object, namespace root or cohort was loaded
or mixed, so h6/h6'/h6'' reconciliation is not exercised. No key/account was
created, used or deleted. No binary, object, ELF or tarball is committed.

Next concrete deliverable: restore the EXACT historical Aeneas executable;
use N73310 with its historical flags, namespace PV_CX_Entry, split-files,
emit-json and the N73309 LLBC, inside the same admission/cap policy. Then
resolve any exact Aeneas refusal through flags/opacity only, build the typed
ExternalTypes/ExternalFuns interface, link function 310 by carrier/type identity
to the existing prover, classify all operations and compile Types then Funs
and the link with standard axioms. Lean 73200–73299 and audits 73297–73299 are
entirely unused. Do not rewrite source or use 562e1f51… as a shortcut.

Final handoff checks are in final-validation.json. The refusal-to-admitted-barrier
interval is 197.232983 seconds. cleanup.json records removal of this job's
compiled Rust target cache only; frozen source and raw/compressed LLBC evidence
remain. No host scope remains running for this job. Stage commits are available
with `git log --oneline 27b582ca44..HEAD`; nothing was pushed.
