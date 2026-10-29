# Event-producing native semantics: acceptance preflight blocked

Branch `codex/pv-evh-20261029`; baseline
`946718387da2351a46a3a095a94f1f003d5f8185`. `DESIGN.md` was committed at
`869852f773` before any Lean. The requested producer is **not implemented**.
The privacy target remains unestablished.

## Exact obstruction

The existing selected extraction's entry is
`ProverRwFull.RealR1_client.prove_for_proof_accounts`, from
`crates/aspis-r1-cost-probe/src/RealR1_client.rs`. It ends at the library retry
owner. `devnet_spend::main`, `plan::run`, and `plan::prove` are absent from the
selected extraction. A repository-wide baseline search of tracked `.lean` and
`.lean.txt` found no `Source: 'tools/r1-cost-probe/src/bin/devnet_spend` provenance
marker (exit 1, no matches). This establishes a tracked-source coverage gap,
not a claim about every untracked file on the host. The existing own host
workspace contains the earlier EVH modules and its env-J configuration; the
read-only inventory is recorded.

Concrete uncovered source operations include main's stdin read/stdout and key
file reads; plan's clock start/elapsed serialization, recovery directory and
file writes/sync, proof and statement writes, returned JSON, and outer error,
panic and runtime termination paths. `rust-effect-anchors.json` pins their
exact baseline lines. It is a direct-call anchor inventory, not a claim of a
complete macro-expanded dependency cone. There is no provenance-backed effect
interface for these executable entries from which to make the requested full
mapping. Network/RPC, allocation, drop, panic/abort/exit dependency coverage must
therefore remain explicitly unresolved, not silently emitted as no events.

The selected `ExternalFuns` has 262 fields, each returning `Aeneas.Std.Result`;
none installs the requested writer. `external-interface.json` contains EVERY
field's type, alias and textual extracted call sites, with conservative effect
classifications and candidate event mappings explicitly labelled UNBOUND. It
is not a reached-call proof or an implemented effect dictionary.

The existing theorem
`R1Z.ProverRwEntropyIteration.no_retry_then_success` (and its entry-specialised
`R1Z.PV_RunJoin_Source.fixed_dictionary_obstruction`) rules out a fixed pure
dictionary representing a reject-zero iteration followed by successful seeds.
The source audit associates that theorem with the actual emitted selected64
loop's ONE `getrandom.fill` (`op129`) on a zero-initialised 64-byte buffer per
iteration. Native source advances the entropy request each iteration. This is
an existing source/interface obstruction, not a new native experiment or a
fresh Lean proof, and not a deployed privacy attack. It does not rule out a
syntax-directed interpreter of a provenance-pinned executable extraction.

`PV_W_ProverEntry.maskedAttempt` leaves the inner prover call as a helper thunk;
`PV_DIAG3.ClientHandlers` leaves successful/error/runtime continuations as
parameters. Using either as though it supplied the missing executable would
fail criteria (a)–(c). The existing `NativePublication55.execute` is likewise a
Result-level source call. Recording events after it returns cannot recover
its failure/divergence prefixes.

## Before / after, validation and witness

Before: 19 OPEN runtime data fields, no full native-event producer.
After: SAME 19 OPEN fields, no full native-event producer. Zero ledger rows
removed, added, or reclassified. Existing compact/published/ops binding is
unchanged; all source/experiment links and LivePublication remain open. No T
field, simulator, observer, native alphabet, frozen source or theorem changed.

No new skeleton or projection theorem is asserted. Consequently there is no
claim of a ruling-(v) joint satisfiability witness. An arbitrary model trace
beside an unrelated publication would not satisfy this task's source criterion.

Validation: `python3 tools/pv-evh3-20261029/audit.py` succeeded (see checks.json),
including all-op inventory, inherited source-resolution SHA checks, baseline
source pins, executable provenance absence and exact entropy-call anchors.
One initial audit assertion expected two fills per iteration; source inspection
corrected it to one. The corrected audit passed. This was a Python audit error,
not a failed Lean attempt, native run, or an extraction-fidelity finding.

Usage: **0/80 Lean, 0 native, 0 Kani**; no env-J IDs consumed, capped scopes
launched, objects loaded or caches changed. No axioms audit or manifest replay
is reported because no Lean source was written or compiled. No build-instance
or source cohort was mixed. The existing host directory was only inspected.
The failed-source-hash launch guard is not exercised: no launch wrapper was
created. No key or account operation occurred.

Stopping point: registered acceptance (a)/(b) fails before Lean. This is not
budget exhaustion, host gating, or successful premise removal. Remaining
budget is unspent; this handoff explicitly reports the unfulfilled task. The
common instructions' rule to stop an item whose target is false/unavailable
prevents replacing the missing executable with a newly invented model and
claiming producer credit.

## Next concrete deliverable

Locate a generation-receipt-pinned existing extraction of executable main and
plan::prove, or produce one with the unchanged pinned extractor, deployed
features/release profile/dependency versions, and the x' toolchain/library
comparison. Extraction must expose the complete effect call cone as syntax,
with continuations retained on failure/divergence, before evaluating Result.
Then implement the writer-world algebra, prove source association rather than
Result erasure alone, install the seven intended projections using unchanged
native projection definitions, and prove the joint publication witness.

D474(C) has not been adopted. The design pins the current baseline; a future
D474 diagnostics extraction can replace the executable reporting subcone and
its source/effect map locally while retaining the separately pinned prover
cone, followed by affected proofs and replay. No hypothetical future row
removal is claimed. The finite-carrier job was not touched.
