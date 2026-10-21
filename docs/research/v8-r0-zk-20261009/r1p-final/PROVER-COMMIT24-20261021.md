# Prover commitment part 24

Base `0b214bdbd`; branch `codex/cx-prover-commit24-20261021`.

Target not yet established. This report is updated after each verified stage.
No file under crates/ or programs/ is edited. The concurrent worker's
SourceIdentification, RustRuntimeJoin and PrivacyR1FinalRelease are not edited.

## Stage 1 — explicit trusted std list

`R1Z.ProverCommitTrustedStd24.TrustedStd` names BTreeMap empty, insert state,
insert previous answer, get, ordered iteration, live-key TLS access and the
single-thread schedule. Every map contract is universal. No field contains
RustProverRefinement, a privacy conclusion, a source caller equation or a
coupling. This is the D133 std trust boundary alongside P6/P7, not a proof of
B-tree internals. It does not enlarge the trusted boundary to samplers.

The API is the successful-operation interface; allocator behavior remains
P6. TLS is one live, typed key, with no thread/key destruction during the
invocation. Trace and PROGRAMMED keys require distinct instantiations.

J7487 is an excluded section-variable elaboration failure. J7488 passes
`R1Z/ProverCommitTrustedStd24.lean`: exit 0, wall 1.40 s, peak RSS
2533360 KiB, swaps 0. All six theorem audits use only
[propext, Classical.choice, Quot.sound]. The exact source SHA-256,
dependency fingerprint, base revision and full audit lines are committed in
`evidence/prover-commit24-20261021/lean/attempts-7487-7489.jsonl`.
The model consistency theorem witnesses a satisfiable list; it supplies no
Rust evidence. No shared predecessor source/object was overwritten.

## Stage 2 — source nonzero counter and adaptive map callers

`ProverCommitCounter24.accounting` proves the exact retained counter for
successful finite executions of the actual extracted coin transition,
counting rejected zero answers. `three_search_room` applies to the three
successive nonzero calls in `sim::tape`, on stream 3 with one counter. If
each finishes within five draws, the final counter is their sum, at most 15,
and another five-word window cannot wrap. `three_agrees` composes all three
finite searches, preserving the counter between them. No unconditional
termination, unrelated-history freshness or whole sim::tape join is asserted.

J7489/J7490 are excluded scalar elaboration failures. J7491 passes the
six-theorem counter module: exit 0, wall 2.03 s, peak 4042632 KiB, swaps 0,
standard three axioms only. Exact receipts and failed sources are retained.

`ProverCommitMapProgram24.run_decode` goes beyond fixed write schedules:
it transports arbitrary finite callers that branch on previous insertion
answers, gets and full ordered iteration. It retains the decoded final
map, every ordered response and terminal output (including caller-selected
errors). `empty_run` uses the trusted empty-map field. The single named
TrustedStd premise supplies every library contract. Source caller-to-program
identification remains separate. J7492 passes: exit 0, wall 1.32 s,
peak 2534100 KiB, swaps 0; both audits use only standard axioms.

The retained ordinary/gamma transcript packets explicitly cover candidates,
not unconditional equivalence to the frozen source. They are not installed
as shipped policies. Further caller/policy/coupling work is in progress.

## Concrete experiment and endpoint

In progress. No premise-removal claim has yet been made.
