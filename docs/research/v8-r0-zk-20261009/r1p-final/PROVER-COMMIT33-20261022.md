# Prover commitment continuation 33

Requested research pin: 26b922be6. Actual worktree base: e4fa76dc15a45abf8b095f39d7390cfad546b8f5 (D145). Branch: codex/cx-prover-commit33-20261022.
Stopped on a demonstrated source-image obstruction. Target not yet established; no endpoint premise removed.

D145 corrects the prior native BTreeMap gate: the standard library is trusted,
not reverified. This continuation checks publication caller logic with an
ordered-list substitute. The sole added TrustedStd field is
`btree_entry_or_insert_with`: a hit retains the map and returns the existing
value without invoking the pure callback; a miss invokes it once, inserts and
returns that value. A boolean invocation trace makes laziness explicit. The
publication callback performs pure field evaluation, not entropy consumption.
No other trusted field is added. This is a named Prop hypothesis, not an axiom.

D143 observable scope: public statement bytes, proof bytes, and answers to
adversary oracle queries. Timing and other side channels are outside the
privacy contract. Internal tables and attempt counts are not published.

## Verification

Env J numbering continues after accepted J9043.
Shared source/object replacements are snapshotted in this branch's host
workspace before installation; dependents needed here will be rebuilt.

Stage 1 checkpoint: J9044 accepts the extended TrustedStd interface and its
model consistency witness. J9046 accepts `ProverCommitPublication33`:
`folded_loop_rec`, `folded_decode`, `folded_loop_decode`, `ordered_consumer`,
and `query_answers`. These are universal loop-denotation/map-interface
results, not yet a source-to-experiment instance. `folded_loop_decode`
preserves callback invocation traces, including duplicate hits. The ordered
consumer permits arbitrary salt-stream transitions; the query answer theorem
retains misses and repetitions. J9045 is a rejected projection-rewrite draft.
All successful checks exit 0 with zero swaps and only the standard axioms.
Complete exact fields and source snapshots are in `evidence/prover-commit33-20261022/lean`.

The source-to-denotation identification is being audited separately with
verbatim shipped loop spans in `harness/native-loops.rs`; surrounding pure
callees and the standard-library map are explicit harness substitutes.
No claim about actual encoding arithmetic follows from those substitutes.
No file under crates/ or programs/ has changed at this checkpoint.

## Demonstrated source-image obstruction (item 5)

J9050 proves `ProverCommitPublicImage33.i_not_source_word`,
`no_total_asset_image`, and `no_total_index_image`. This is a mathematical
counterexample to a field-preserving source image on **every model statement**,
not a tool timeout. `PrivacyR1AcctBasis.K` is `WideExact`, not M31.
`R0P.Public K.assetId` can equal the tower element `i`, which is outside the
image of the M31 algebra map. Independently, `nextPairIndex : Nat` can equal
`2^64`, which has no exact u64 representation. The shipped `Public` uses
`M31` public cells and `source.next_pair_index : u64`.

This does not disprove privacy on admitted/source-representable statements,
and does not rule out a non-field-preserving byte projection on unreachable
statements. It does refute the literal universal, field-preserving source-image
interface needed to identify the same public statement. Merely being typed in
K does not prove membership in the source M31 image, nor bound the Nat index.
No invented public-byte error value, truncation, or new admission premise has
been introduced. The existing theorem and security target are retained.

Exact next interface: define a canonical source public image on the admitted
statement carrier, prove all public cells lie in the M31 image and the pair
index is below `2^64`, and prove the actual `Public::public_bytes` returns
`Ok (pubBytes x)` on that image. If the target must quantify over every
unrestricted model statement, specify and justify its behavior for the two
counterexample shapes above; that cannot be a field-preserving image. Changing
the carrier or adding such a premise is not a deletion-only endpoint edit.
The literal item 5 is stopped under common rule 4; no restriction is silently
added to make it true.

J9047 also accepts first-conflict transcript merge transport through the
existing insert-state/previous and ordered-iteration fields. J9049 connects
the extracted sorted lookup to the std graph lookup, retaining an explicit
numeric-sortedness hypothesis. J9051 rebuilds the unchanged adaptive map
program after the TrustedStd source/object replacement. All new statements
have `#print axioms`, accepted checks have no nonstandard axioms, and no
unchanged full regression has been rerun.

The bounded folded single-transition gate passes against the sorted-list
substitute, including an arbitrary pre-existing entry and both lazy hit/miss
paths. The exact accepted harness source is retained in `input-snapshots/merge-v1` and its hashes match the `folded-step-v1-inputs.json` receipt; that later snapshot name does not imply a successful merge check.

## Verbatim endpoint before/after

The endpoint is byte-identical to the actual part-33 base `e4fa76dc1`. This records zero premise
deletions, not a completed specialization. Full before/after modules and an
empty diff are retained under `endpoint/`; all surrounding parameters,
quantifiers, carriers, failure events, and budgets remain unchanged.

Before:

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))


theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))


theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```


## Final evidence and bounded-check scope

The accepted Kani check is `proofs::folded_loop` (`folded-step-v1`): exit 0,
30.781 seconds wall, 2,054,348 KiB GNU-time peak RSS, zero swaps. It checks
one verbatim source-loop transition with an arbitrary byte-sized query and
an arbitrary optional pre-existing entry, including independent old/new bytes.
The query's `/4` grouping and lazy callback invocation count are preserved.
The stub is a sorted four-slot association list; capacity is an assertion,
not an assumption, and is unreachable inside the checked bound. It realizes
the successful TrustedStd map contract on the bounded states tested; it is
not a proof of an unbounded implementation of std. Pure `eval_at`/`encoded`
callees are explicit byte-valued substitutes. No field-arithmetic or actual
encoding correctness follows from that check. The universal Lean theorems
consume the named std contract directly, not the finite capacity stub.

The full source-loop body spans for folded publication, leaf construction,
query-order serialization and transcript merge are mechanically extracted
and source-hashed by `harness/generate.py`. Only the folded transition has
an accepted Kani receipt here. The combined leaf/serialization harness is
not run; transcript merge diagnostics have no accepted Kani result. Earlier
whole-loop diagnostics were intentionally stopped while reducing loop and
allocation expansion, with no cap increase. `folded-v2` reports CBMC status 6
through the terse wrapper (not a counterexample); `folded-v3` exits 2 for
incompatible Kani output/jobs options. `merge-v2` was stopped after the
source-image obstruction was demonstrated. Stopped commands exit 143 and
are not promoted to results. Their wrapper RSS can omit killed descendants;
`cgroup_memory_peak_bytes` in each receipt is the aggregate scope metric.

Every Rust command uses its own 6G/8G/zero-swap/64-task scope, four Cargo
build jobs and four linker threads. Time is in CBMC symbolic verification,
not native finite-field arithmetic; Kani's dev-profile MIR compilation is
recorded exactly, not reported as a release arithmetic gate. No dense
arithmetic gate or SBF build is run in this continuation.

Final accepted Lean sources and dependency-object fingerprints are checked
by `final-proof-audit.json`. Each attempt's exact command/target, source SHA,
exit, wall time, peak RSS, swaps, revision/base-plus-source-overlay and complete
`#print axioms` lines are retained in `lean/attempts.json`, source snapshots,
and raw receipts. The initial host checkout revision is e4fa76dc1; subsequent
proof overlays are identified by their exact source hashes, not attributed to
that base commit. Rejected J9045 and J9048 drafts remain separate. J9052 is
the final focused dependency-cone/axioms audit. All accepted axioms are subsets
of `[propext, Classical.choice, Quot.sound]`.

| Final module | Env J | Exit | Wall | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|---:|
| R1Z/ProverCommitTrustedStd24.lean | 9044 | 0 | 0:01.76 | 2532472 | 0 |
| R1Z/ProverCommitPublication33.lean | 9046 | 0 | 0:01.60 | 2527040 | 0 |
| R1Z/ProverCommitMerge33.lean | 9047 | 0 | 0:01.31 | 2535772 | 0 |
| R1Z/ProverCommitSortedStd33.lean | 9049 | 0 | 0:01.47 | 2523328 | 0 |
| R1Z/ProverCommitPublicImage33.lean | 9050 | 0 | 0:04.63 | 4079416 | 0 |
| R1Z/ProverCommitMapProgram24.lean | 9051 | 0 | 0:01.44 | 2543868 | 0 |
| R1Z/ProverCommit33Audit.lean | 9052 | 0 | 0:01.82 | 4085588 | 0 |

## Retained obligations and stopping state

Stage 1 remains partial: universal folded/map/merge denotations and the sorted
lookup graph are proved, but the complete native opening/folded/programming
publication owner is not. The numeric-sortedness premise in `lookup_tree`
remains explicit; no general source-caller law is hidden inside TrustedStd.
Exactly one trusted field was added: `btree_entry_or_insert_with`.

Stages 3–4 are not closed: there is no new certified eight-attempt publication
owner or actual `prove_masked_retrying_with` entropy/reservation owner. The
inherited explicit OS failure/zero-draw exhaustion events and their unresolved
OS-law/durable-store boundaries remain unchanged. Stage 5 stops on the two
proved field-preserving source-image counterexamples. Stage 6 remains open:
no `shippedProverExperiment`, no concrete real/ideal WholeRunJoins, and no
endpoint premise deletion. The verbatim before/after above and empty endpoint
diff attest to that unchanged statement, not to completed specialization.

The next concrete deliverable is the source-representable public interface:
prove representability for the actual honest builder's public range, fix the
canonical public serialization, and specify behavior for unrestricted model
records outside that range. A public-byte projection alone must not be
silently substituted for preserving the same statement's semantic fields.
The counterexamples do not prove the admitted privacy endpoint false; they
show why D143's "typed in K, hence canonical" reasoning is insufficient for
its literal universal source-image obligation.

No files under `crates/` or `programs/` changed; `shipped-sources-unchanged.json`
records the assessment. The shipped-file ELF rebuild rule is therefore not
triggered; part-32 artifact evidence is reused as historical evidence only.
No full formal manifest is launched because the source-refinement preflight
is not green. No unrelated runtime/adversarial suite is repeated. Host caches
and retained sources remain; this job's active processes have been stopped or
completed. No local target directory, wallet, or key was created or deleted.
Nothing was pushed, merged, or written into another worktree.

**Target not yet established.** Stop on the demonstrated universal public
source-image obstruction rather than adding an unannounced admission premise.
