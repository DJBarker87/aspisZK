# Oracle port continuation 6

Unmerged draft on `codex/cx-oracle-port-draft-20261021`; no push is authorized.
Only new `OraclePort` Lean modules are authored. Existing soundness endpoints,
S-cone candidates and concurrent M10 instrumentation are unchanged.

## Selected observations

`OraclePortSelectedObservationsC6` projects the matching reader to its scalar
record (both whole words set to zero), the first fold at each of 22 queries,
the opened V value, and the second fold of each queried final fibre.
`Writer` and `Backend` are predicates over that observation and the query/rho
scalars. `observe_withWords` proves invariance under agreement of the selected
initial fibres, selected V coordinates, and selected final fibres.
`typed_accepted` derives these checks from D0 acceptance. `stored_accepted`
instantiates this at the specified C4 stored decision, retaining its exact
parser and query identities. It does not identify that decision with Rust.

## Semantic reader and consumer

`OraclePortSemanticObservationsC6` erases only the whole C2 callback. Its
parser law includes failures and proves that word enrichment preserves this
scalar view. `OraclePortSemanticProjectionC6` proves equality of the exact
claim, polynomial and challenge projections consumed by R3. The callback is
retained in the classifier/extractor's literal messages.

`OraclePortReaderPlumbingC6`, `OraclePortOpeningRewordC6` and
`OraclePortMatchingRewordC6` prove successful reader reconstruction. The
matching result is exactly `withWords` of the old scalar data and the new
words. `OraclePortSelectedConsumerC6.toLiteral_nonempty` converts selected
checks to the existing `LiteralAcceptanceTerminal.Checks`;
`OraclePortCleanObservationsC6.clean_of_observations` supplies the existing
clean consumer with that interface. Thus there is no remaining consumer
requirement to equate candidate and recovered full rows.

`OraclePortObservationTransportC6.transport` is the selected version of that
consumer join. `OraclePortMapObservationsC6` lifts packed-map agreement through
the total decoders. `OraclePortAllSelectedRecoveryC6.authenticated` composes
indexed recovery for all 22 positions and both batches. The candidate word
identities and this recovery feed `OraclePortRecoveredAcceptanceC6`.

`OraclePortReachedRunC6` derives acceptance, trace containment, consistency,
first-read bounds and actual frame reads on the adaptive stored experiment.
`OraclePortParsedRootsC6`, `OraclePortRootBytesC6`, `OraclePortFrameShapesC6`
and `OraclePortReachedRootsC6` derive the three root/frame identities.
`OraclePortActualAcceptanceC6.accepted_checks` then has no independent
containing log, frames, root identities, authenticated maps, or source-data
parameter. It returns checks on restored rows carrying the compiler's exact
`wordsFromRun` of the actual original log.

`OraclePortRowsCanonicalC6` proves the restoration identity under the
constructor schedule. `OraclePortCanonicalAcceptanceC6` derives that schedule
from accepted Guard and the existing erasure-preserving canonical prover,
then identifies the restored rows with the **actual annotated rows**.
Finally `OraclePortStoredAcceptanceC6.checked_acceptance` proves

```lean
OraclePortStoredChecksC4.CheckedAcceptance D decision (canon P) (Q+1161)
```

from only the prover's issued-query bound. Its acceptance and the same
recorded binary-collision guard are the quantified conditions of that
interface. `original_clean` derives the original-log exclusion from the
recorded guard. There is no `ReaderBinding`, free source/data/context,
matching equality, writer equation, semantic equation or backend model
hypothesis in this theorem. This closes those **local model obligations**;
it is not a premise-deleting rewrite of the global v3 signature.

## Accepted context and endpoint comparison

`OraclePortAcceptedContextC6.context` derives the model context from one
accepted parser/input/opening-view witness: state32, the two semantic roots,
ten semantic challenges, four circle coordinates, and the batched opening
claim. The claim is `JointFunctionalBinding.claimedValue`, not row 14's
semantic claim. `accepted_context` binds physical decoding and the six-read
write/resume Program to that same witness.

`OraclePortCheckpointObservationsC6` proves that selected final-fibre
agreement preserves the recomputed model, authentic saved bytes (including
the reached-ten state and checksum), and write/resume values. Whole-word
agreement is unnecessary here too. Frozen Rust/account/caller refinements
and duplicate-query validation are not implied by these byte-model laws.

### The retained global consumer has a different carrier

The direct inherited consumer application was type-checked and rejected;
its source and exact error are retained as
`OraclePortLegacyCarrierDiagnosticC6.lean.txt` and the attempt-1 receipt.
The error is not a theorem failure inside selected arithmetic:

```text
OraclePortReachedRunC6.decision
has type OraclePortStoredExperimentC4.Decision
but is expected to have type OraclePortExperiment.Decision
```

Verbatim carrier definitions:

```lean
abbrev Decision := Bytes → OraclePortExperiment.Decision
abbrev Prover := Program Bytes State Input
```

The stored input includes `statement`, `proof`, and `stored`. The inherited
`OraclePortConsumer` takes the old prover returning only `(public, proof)`;
the landed headline v3 is narrower still, taking a pure
`d : ErasedPrefix → ErasedMessage → Bool`. Fixing `stored` separately for
each oracle world is only a pointwise projection, not an equality of
adaptive experiments under their probability law. C4's projection theorem
explicitly has that scope.

The direct global-headline substitution is therefore stopped at this
ill-typed join, as required by the common rules. A new stored-carrier
LazyInj/clean-model/probability composition (or a proved protocol-carrier
lift) is still required. This report does not claim that no such bridge can
be proved. It does not relabel the C4 decision as a completed frozen dV.

### Comparison against landed headline v3

The comparison revision and full snapshots are pinned in
`OraclePortC6Comparison.json`. Both preserved signature diffs are empty:
**zero claimed headline premise deletions or replacements**. These are
preservation audits, not a deletion-only specialization of an unproved
endpoint.

| Landed v3 item | Continuation 6 result | What remains for a dV numeric headline |
|---|---|---|
| Pure free `d` / old prover pair | Specified C4 stored oracle decision, actual adaptive stored input and exact recovered words | Stored-carrier probability/consumer bridge; frozen execution identification |
| R16 model fields | Accepted parser/public/query/rho fields are constructed | Instantiate the global consumer on the new carrier |
| R13 model matching | Exact matching-reader transport and actual-log selected recovery | Same carrier bridge; no whole-row equality premise |
| R15 writer | Selected first matches transfer to recovered words | Frozen writer/caller refinements remain |
| R3 semantic | Exact claim/polynomial/challenge observations transfer; parser supplies degrees | Frozen semantic/circle refinements remain |
| R14 model backend | Pairing/ClosedSum transfer; checkpoint saved bytes and resumed value are invariant | Frozen arithmetic/ABI/account/caller refinements remain |
| R-wire/tag | Accepted Guard and aligned parser retained; literal decoder model unchanged | Stored-carrier completion/injection composition |
| TX1 / Pool TX2 | Accepted model context now fixed to reached data; authentic physical save/resume model | Account/policy/provenance and global deployment transport |
| Concrete M10 / v3 log-size closure | Untouched | New carrier's `Q+2322` issued-log envelope cannot be silently replaced by old `Q+1161` |
| Numeric deployed-failure conclusion | Existing R19 and landed v3 source preserved | No completed-dV numeric theorem is claimed |


## Receipts

Every attempted compile is retained in the evidence directory's `manifest.json`
and its module/attempt directory, including failures. Each receipt records the
exact command/target, revision, source SHA-256, direct object hashes, dependency
fingerprint, exit, wall time, peak RSS, process swaps and full axiom lines.
No cap or heartbeat limit is raised and no unchanged attempt is repeated.

## Verification freeze

The focused audit passes for 24 final new modules and 94 final axiom reports
(90 theorem declarations plus audited definitions). There were 62 proof
compile attempts: 24 succeeded and 38 retained local elaboration/proof
failures. The separate deliberate carrier diagnostic failed as expected;
three dependency preflights were rejected before Lean launched. All formal
attempts reported zero process swaps; peak RSS was 3,659,874,304 bytes.
Every final axiom set is a subset of `[propext, Classical.choice, Quot.sound]`.

The audit verifies every source snapshot and receipt, final source/import
object hashes, no unchanged attempts, theorem axiom-report coverage,
new-module-only Lean scope, and unchanged retained headline snapshots:

```sh
python3 -B docs/research/100bit-spend-path-20261013/evidence/oracle-port-draft-20261021/OraclePortContinuation6Audit.py
```

These are focused model-proof receipts, not a frozen-verifier formal release.
No unfinished global manifest is replayed. No shipped code, existing Lean
module, concurrent worker file, wallet key or deployed artifact was changed.
All stage commits remain on this draft branch; no push or merge was performed.
