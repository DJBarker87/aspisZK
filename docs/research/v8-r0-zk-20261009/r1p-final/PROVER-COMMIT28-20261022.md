# Prover commitment part 28

Base `26b922be6`, branch `codex/cx-prover-commit28-20261022`.
Target not yet established. Work and evidence are recorded incrementally.
The final assigned Env J range is 7800–7999; used receipts are skipped.
No shipped files or concurrent-owned modules are changed.

## Continuation port

The retained control21 suffix contains scanner selection, all 22 trace writes,
query rejection and rho. The port uses an explicit state transformer over
Aeneas Result, with pure Result operations lifted into it. Digest calls consume
the current machine state instead of the stale copied hash token. The full
returned machine is observable at the continuation boundary. A mechanical
source-port check will retain every non-digest operation in order.

Pending: generic interpreter validation, the concrete suffix, semantic/circle
and full walk composition, replay reset, retry/programming/serialization,
shippedProverExperiment, both WholeRunJoins and endpoint specialization.
RustProverRefinement remains explicit until those concrete obligations close.

## Stage 1 — complete suffix, with source reconstruction

`ProverCommitStateLift28.bind_run` proves the generic state-threading equation;
`install` transports a per-call implementation equation through any complete
stateful continuation. `ProverCommitControlProgram28` is a mechanical monadic
lift of the seven retained control21 functions. Pure Result specialization
reconstructs every retained source body (`ProverCommitControlSource28`), including
the whole query scanner/trace continuation and tail. These are kernel-checked
identities, rather than a syntactic diff offered as a source theorem.

`ProverCommitControl28.query_effects` and `tail_effects` install the actual
extracted CoinOracle and the concrete D136 scalar/query policy. Their complete
results retain the external machine, including on inner verifier errors. The
old dictionary/token is no longer the mutable-state carrier. No source-join
hypothesis is added: the only per-call equality is the proved `call_exact`.

J7800 (generic state equations), J7809 (seven source reconstruction audits) and
J7813 (two concrete complete suffix audits) pass, with standard axioms only,
zero swaps, respectively 1.77/3.97/2.27 s and
4157784/4200924/4181032 KiB peak RSS. The first direct `rfl` reconstruction of
the query/tail exceeded default recursion depth; J7807/J7809 replace it with
per-bind congruence and previously proved helper equations. No limits rose.
Earlier parse/name diagnostics and exact snapshots are retained and excluded.
This stage does not claim a full walk, retry or serialized-game join.

The same construction now reconstructs the full semantic and circle callers
(J7814: four audits, 1.76 s, 4151548 KiB, zero swap). The validators and scalar
samplers remain the actual retained functions. `ProverCommitSemanticRows28`
ports the finite 25-row loop and proves equality with the actual extracted
loop under its unchanged row-count invariant, then installs the concrete
machine (J7816: three audits, 1.88 s, 4167424 KiB, zero swap). J7815 recompiles
the final generic suffix after its explanatory comment changed. All accepted
new theorems audit to the allowed standard axioms or fewer.

## Stage 2 — ordered observations and composed walk continuation

`ProverCommitLogged28` adds an ordered call/answer list alongside the native
machine: the D133 recording map alone cannot represent repeated reads.
`query_history`/`tail_history` install the complete suffix with this observer.
`replayReset` retains the exact finite tape and prior ordered history, resets
the cursor to zero, enables a fresh empty recording map and clears collision;
`reset_then` proves the next continuation receives precisely this state.
J7817 passes six audits (2.30 s, 4188872 KiB, zero swap).

`ProverCommitWalk28.continuation` composes the 25 semantic rows, both concrete
circle policies, nominal coefficient-preserving conversions, and the complete
suffix. `continuation_effects` installs the actual extracted machine in the
whole composition, retaining all early inner errors and ordered reads. J7820
passes (1.86 s, 4165360 KiB, zero swap). This begins **after** semantic
initialization and is a constructed formal continuation, not yet an extracted
native `walk` owner theorem. Its documentation preserves that boundary.

`ProverCommitPortMarginal28` extends the D134/D135 marginal construction to
arbitrary stateful continuations and arbitrary observations of the result,
final machine and ordered history. No finite-call-tree adapter, successful-run
conditioning or extra randomness is required. J7821 passes three audits
(1.77 s, 4160768 KiB, zero swap). These are marginal laws, not source/model
pointwise walk equivalence or WholeRunJoins. All audits use standard axioms.

## Stage 3 — actual initializer and demonstrated native-owner obstruction

A tiny extraction-only wrapper calls the unchanged native
`SemanticTranscript::new`. `init28-v2` extracts the actual checked public-length
conversion, rejection before any digest, complete domain framing and returned
initial state. Its function body is retained verbatim. The pinned generator's
global Error-discriminant collision is replaced by an explicitly named local
instance with identical variant indices. `Result::map_err` is defined by
ordinary Ok/Err case analysis; no template axiom is installed. The first
`init28-v1` root pattern selected no body; its exit 0 is explicitly excluded,
not represented as successful initializer extraction.

`ProverCommitInit28.source` reconstructs the actual extracted initializer from
the generic monadic one, including length errors. `walk` now includes this
initializer and the entire constructed continuation. `walk_effects` installs
the actual extracted CoinOracle with final machine and ordered history.
J7830 passes both audits (1.97 s, 4160448 KiB, zero swap, standard axioms).
This is a full constructed formal walk, **not** the missing native outer-owner
equality, retry/serialization join or shipped experiment.

The necessary native-owner extraction was attempted on just `sim::walk`.
Charon succeeds (`walk28-v1-charon`: exit 0, 30.917 s, 578312 KiB, zero swap).
Aeneas fails (`walk28-v1-aeneas`: exit 2, 0.814 s, 120912 KiB, zero swap):

```text
Failure "Could not match the contexts"
Source: 'crates/aspis-r1-cost-probe/src/sim.rs', lines 165:4-177:1
Compiler source: interp/InterpJoin.ml, line 2209
```

The retained contexts identify the `Range<u8>` semantic loop, `sem:[QM31;25]`,
borrowed `Records`, and pending early return. This is a translation/borrow-join
obstruction, not memory pressure or a privacy counterexample. No unchanged
retry, raised cap, new cryptographic assumption, or full 115-word harness is
used. Raw logs, exact extraction commands, source/tool hashes, caps and
reservations are committed under this job's evidence directory. All extraction
work is optimized; time is in compilation/translation, not elimination.

**Exact next interface:** prove the native `walk` semantic-prefix owner
(`sim.rs:165–168`, including indexing and `map_err`/early return) equals the
bounded 25-row stateful `ProverCommitSemanticRows28.rows` owner, then compose
its returned state through both circles and the suffix. A per-step owned Rust
loop shell with Kani source-equality gates is the next replacement for the
failing borrowed iterator extraction. The existing `extracted_source` theorem
is for the retained `semantic20.rows` helper, not this native outer loop; the
two are not silently identified.

Following that interface, connect replay to the actual attempt owner: retries,
P_R1 check, tape/view builders, commitment programming, ordered serialization
and table merging. Those concrete joins remain open. `shippedProverExperiment`
and real/ideal WholeRunJoins are unconstructed; realBad/selectedBad, seedGuess
and fuel exhaustion events are unchanged. RustProverRefinement remains explicit;
zero premises removed. Target not yet established.
