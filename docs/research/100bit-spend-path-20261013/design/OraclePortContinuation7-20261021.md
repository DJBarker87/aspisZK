# Oracle port continuation 7

Unmerged draft on `codex/cx-oracle-port-draft-20261021`. No push or merge.
Only new `OraclePort` modules are authored; existing modules and concurrent
worker files are unchanged.

## Stage 1: stored-aware probability consumer

`OraclePortStoredReductionC7` constructs `fixStored` by an oracle-independent
map on the prover's output. `pairProver` erases that extra input only after
canonicalization. Its oracle program is independent of the fixed bytes;
`annotated_selected` identifies its recorded execution with the projected
adaptive execution at each selected oracle world.

`OraclePortStoredConsumerC7` applies C6 `checked_acceptance` to each fixed
fibre, derives completion and the built-in tag law, and obtains the inherited
clean model pointwise. No fixed fibre replaces the adaptive experiment under
the probability law. This closes the carrier obstruction recorded in C6.

`OraclePortPureOutputC7.lazyMean_map` proves equality for every observable
under the actual lazy memoized oracle law. `OraclePortStoredProbabilityC7`
applies the existing binary collision mass and classifier start union bound
to the projected adaptive program, with unchanged kappa and B. Its final
bound is stated directly on the stored carrier too:

```lean
lazyMean (annotated D dV (canon P)) emptyTable (fun v => failureMass (view v)) ≤
  BinCombinedMerkleCollision.kappa (Q+1161) +
    ((Q+1080 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126
```

The distinct-read budget is Q+1161, start budget Q+1080, and issued-log
length Q+2322. These are separate bounds; none is substituted for another.
The extra stored bytes are returned by the prover, potentially after
adaptive oracle calls, and are never selected by an oracle-dependent external
parameter.

## Stage 2: headline

`OraclePortHeadlineDVC7.lean` proves `OraclePortHeadlineDV.final_soundness`.
Its conclusion contains the concrete extractor cost, returned-witness
relation, abort allowance, total envelope and per-query failure bound.
`per_query` exposes the numeric field directly. There is no generic cost
ledger premise: the closed M10 ledger used by the pinned v3 headline is
reused read-only at budget Q+1161. `accepted_cost_cubic` proves the resulting
bound 4·scale³·(Q+2323)³. No M10 instrumentation source or object is rebuilt.
The exact foreign-cache command/source revision is recorded in
`OraclePortC7M10ImportPin.json`; this imports existing results, not a new M10
claim or a merge of another worker's files. Those newer M10 source modules
are not added to this worktree: integration must supply the pinned M10
source closure from that revision. `OraclePortHeadlineLedgerC7` also retains
a generic, locally sourced ledger composition for independent review.

Two explicit joins remain, with their complete definitions in
`OraclePortRuntimeBindingC7`:

```lean
def ExecutionJoin (D : LiteralByteProtocol.Decoder) (rust : Verifier) : Prop :=
  ∀ i : Input, rust i = verifier D dV i

def StoredCarrierBinding (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (runtime : Runtime) : Prop :=
  ∀ H : Bytes → State, ∀ run : RunView,
    (eval H runtime).2 = some run → run.2.2 = true →
      run = eval H (annotatedWith D rust (canon P))
```

`rust` denotes a supplied source verifier oracle program, not a proved
extraction of frozen Rust in this packet. `runtime` is a supplied stored-aware
runtime program returning an optional complete run. The first join must
establish equality of all reads and verdicts, including rejected inputs;
the second binds the accepted resumed run's full stored input, metadata and
trace in the same oracle world. Neither join is proved here. They are the
remaining source/caller obligations, not renamed R16/R13/R15/R3/R14 model
checks. The transport theorem has no probability-law premise: it derives
the law from this pointwise runtime binding using finite-support oracle
averaging. The headline includes one scan allowance, as v3 does.

The model `dV` is exactly `OraclePortStoredDecisionDraftC4.decision` as used
by C6, now supplied with a completed probability consumer. Calling this a
completed **draft model headline** does not identify it with frozen Rust.
The `ExecutionJoin` is where that identification remains to be proved.

## Stage 3: premise and numeric comparison

Comparison is pinned to revision
`5efd4f378b9f772bbe18daf428a0b6da80501141`, the same v3 source snapshot
used in C6. The current worktree's R19 and earlier headline sources remain
unchanged. Full comparison metadata is in `OraclePortC7Comparison.json`.

| Item | Pinned R1FinalSoundnessHeadlineV3 | OraclePortHeadlineDV.final_soundness |
|---|---|---|
| Decision / prover | Free pure `d`; prover returns `(public, proof)` | Fixed stored oracle model dV; prover returns `(public, proof, stored)` |
| R16 instance | `h_R16_instance` and free `source` | No premise: accepted parser/public/query/rho fields feed C6 checks |
| R13 matching | `h_R13` | No premise: C6 actual-log recovery and selected-reader transport |
| R15 model writer | `h_R15_writer` | No premise: selected first-match checks transported to recovered words |
| R3 semantic | `h_R3_semantic` | No premise: exact claim/polynomial/challenge projection and accepted degree checks |
| R14 model backend | `h_R14_backend` | No premise: pairing and ClosedSum transported by C6 checks |
| ReaderBinding / free matching or word equality | Historical local frontier | Absent; not reintroduced by the probability reduction |
| Decoder completion / tag | `h_Rwire_tag`, then inherited completion | No premise: dV Guard gives tag, Checks give format, completion follows |
| Frozen source execution | Free d linked only through supplied model/evidence obligations | **Added:** `h_Rust_equals_dV : ExecutionJoin D rust`, complete oracle-program equality |
| Runtime / Pool | Constructed pair-carrier Pool `tx1` / `poolTx2`, tape and policy | **Added:** `h_stored_runtime : StoredCarrierBinding D rust P runtime`; generic stored-aware runtime supplied explicitly |
| Boundary inventory `s`, `evidence` | Standalone opaque boundary statements and evidence | No standalone record; this does **not** prove its source/security claims. Concrete source/caller compliance remains in the unproved joins |
| M10 | Closed concrete extractor/ledger, no adequacy premise | Same pinned concrete extractor/ledger, instantiated at Q+1161; no adequacy premise |
| Collision / per-start density | κ(Q+1161), B=15/2¹⁰⁹ | Unchanged κ(Q+1161) and B |
| Start multiplier | Q+34 | Q+1080; envelope increases exactly by 1046·B |
| Abort / scan | 2⁻¹²⁶ and one 2⁻⁴⁵⁴ allowance | Unchanged |
| Per-query conclusion | failure ≤ (Q+1)·2⁻¹⁰⁰ for 0 ≤ Q ≤ old Qmax | Same form for 32 ≤ Q ≤ new Qmax |
| Upper Qmax | 14777960484892959601791002642008314224629686680 | 14777960484892959601791002642008314224629686649 (31 smaller) |
| Issued recorded log | ≤ Q+1122, weakened to Q+1161 for ledger | ≤ Q+2322 |
| Concrete cost | ≤ 4·scale³·(Q+1162)³ | ≤ 4·scale³·(Q+2323)³; degree remains 3 |

### Exact deletion audit and its scope

The v3-to-dV theorem changes the carrier, fixes the decision, changes the
runtime subject and constants, and exposes two joins. It is **not** presented
as a literal deletion-only edit to the old theorem. The entire structural
signature comparison is `OraclePortC7-v3-to-dV-structural.diff`.

The individual premise-removal audits use a controlled same-carrier
normalization: fixed stored fibres with the same public/proof carrier as the
inherited consumer, oracle decision `dV s`, and `pairProver s P`. The checked
module `OraclePortPremiseDeletionC7` gives successive signatures deleting
exactly R16, R13, R14, R15, R3, the tag law, and finally the free source.
Each `OraclePortC7-delete-h_R*.diff` contains only that deletion; each
`OraclePortC7-h_R*-verbatim.lean.txt` quotes the exact audited premise.
These are compatibility adapters, intentionally carrying now-redundant
hypotheses: their proof is the independently derived `fibre_clean`, not an
attempt to prove arbitrary source witnesses correct. The original v3
boundary-evidence antecedents are omitted in this normalization because the
new model theorem has no boundary-evidence argument. No cross-carrier
logical weakening is asserted merely by renaming syntax.

At the **completed dV headline itself**, the controlled before/after pair is
`final_soundness_of_clean` / `final_soundness`; its only deleted premise is,
verbatim:

```lean
(h_model : CleanAcceptedModel D (projected D P) (bad Q))
```

`OraclePortC7-delete-model.diff` verifies that one deletion, with the theorem
name and location of the signature colon normalized identically. Every
other parameter and the conclusion are identical. The proof passes
`OraclePortStoredConsumerC7.clean`, whose fibre Checks come from C6
`checked_acceptance`, and hence no separate instance/matching/writer/
semantic/backend/completion assumption is hidden in the completed headline.

These proofs do not supply the actual frozen `rust`, runtime implementation,
or the two join proofs. The shipped Rust and all existing Lean modules are
unchanged. A release still needs those joins and its own exact artifact
and deployment evidence.

## Evidence

Focused attempts are recorded in
`evidence/oracle-port-draft-20261021/OraclePortContinuation7Manifest.json`.
Each compile has its exact target/argv, source revision and SHA-256, direct
import object hashes and dependency fingerprint, exit, wall time, peak RSS,
swaps, complete axiom lines and errors. Failed attempts are retained. Local
compiles use the shared lock and -j1 -M4400 -DElab.async=false; no limit is
raised. Only standard axioms are accepted in final results. No full release
manifest, generated certificate aggregation, Rust build or wallet operation
is part of this draft proof change.


## Final focused freeze

`OraclePortNumericComparisonC7` proves the exact envelope increase 1046·B,
the 31-query maximum shift, and that the larger cubic cost budget is at
most eight times the old cubic budget. These compare the same symbolic
constants without evaluating a generated recurrence or large state space.

The one final focused import replay is `OraclePortFreezeC7` attempt 1:
exit 0, 5.5168143748 s wall, 3,596,238,848 bytes peak RSS, zero swaps. It
imports the completed headline, checked premise-deletion adapters and numeric
comparison, and audits all three public endpoint theorems. The packet freeze
pins every final new source in `OraclePortC7FrozenSources.json`.

Final totals: 11 new modules; 18 compile attempts (11 successful, 7 retained
failures); 41 final axiom reports (38 distinct declarations, including one
audited definition and the three repeated public endpoint audits); every
final axiom set is a subset of `[propext, Classical.choice, Quot.sound]`.
Maximum RSS over this packet's attempts is 3,668,852,736 bytes; every attempt
reported zero swaps. No unchanged source/dependency pair was recompiled.
The failed proof attempts were fixed by statement/plumbing/proof structure;
no memory, recursion, heartbeat or exponentiation limit was raised.

The read-only audit checks all receipts, exact source/import object hashes,
dependency fingerprints, final objects, theorem axiom coverage, source freeze,
accepted pinned M10 object/source provenance, individual deletion-only diffs,
and the unchanged retained v3 snapshot:

```sh
python3 -B tools/oracle-port-c7/audit.py
```

An initial audit-harness pin referenced the historical M10 attempt-1 command,
which had failed. The pin was corrected to accepted attempt 4, whose source
and object SHA match the actual cached import. Both commands have identical
search paths. No Lean rerun or M10 object change resulted; the preflight
journal preserves this correction.

As in LOG D63, focused compilation against pinned historical objects is
not a clean ordered rebuild of one historical source closure. The release
manifest remains separate. This packet proves the requested draft model
composition; the exact Rust execution and stored runtime joins remain
unproved. No shipped code, existing Lean module, S-cone candidate, M10
instrumentation source, wallet key or deployed artifact was changed.
