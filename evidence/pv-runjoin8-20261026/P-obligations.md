# Exact P inventory at entry and current prepared state

Notation is the notation of PV_RunJoin_TrustLedger and TrustEndpoint, without
changing the underlying quantifiers. `h` is the exact installed
PhaseWireLog2Bin.honest BuilderSource.prover; `source` is the unchanged
ProverCommitReencode16.experiment; `runtime`, `boundary`, `oldBad`, `queries`,
`State` and `World` have the exact definitions in those modules. The complete
binder context and statements are retained in before-statements.lean.txt.
The current accepted AFTER list equals BEFORE: all new work is uncompiled.

## Candidate premises before

Dictionary identity:

```lean
∀ hh xx ww ss, PV_RunJoin_MapErrInstalled.Identity ((inputs hh xx ww).ops ss)
```

Common public inputs:

```lean
∀ (w : h.Instance), h.public w = x.1 → ∀ s : State,
  (inputs h x w).ops s = (common x).ops s ∧
  (inputs h x w).pub s = (common x).pub s ∧
  (inputs h x w).hash s = (common x).hash s
```

Initial ledger independence:

```lean
∀ (t u : Fin 128 → ProverCommitPublicNonce40.Raw) (rest : Rest),
  boundary.ledger (PV_RunJoin_Deployed.initialState runtime
    (boundary.coordinates.symm (t,rest))) =
  boundary.ledger (PV_RunJoin_Deployed.initialState runtime
    (boundary.coordinates.symm (u,rest)))
```

Causal frames:

```lean
∀ (i : Fin 128) (t u : Fin 128 → ProverCommitPublicNonce40.Raw) (rest : Rest),
  (∀ j : Fin 128, j.val < i.val → t j = u j) →
  boundary.frame i (t,rest) = boundary.frame i (u,rest)
```

Complete extracted trace:

```lean
∀ (adv : R1Adv K CommitHandle Aux) (w : h.Instance), h.public w = x.1 →
  ∀ r : World,
  ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
  extracted r.coins adv w =
    source.real h B outputs
      (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1
```

The draft InstalledTrustLedger.proofs derives identity and common_public from
the PUBLISHED InstalledFamily.map_error and .public_common, at the SAME
SourceSelectionContract.Data and codec-selected input family. It does not
remove Data.publicBinding, whose exact statement remains:

```lean
∀ h x w, h.public w = x.1 →
  PV_Src_NativeInput.publicInput (selection.selected h x w) =
  PV_Src_NativeInput.publicInput (selection.publicRecord x)
```

The CausalTrustLedger draft constructs the initialized ledger from the
residual coordinate and the frame from a strict prefix. The original initial
and causal equations are then conclusions, retaining the original trace
premise. This is a constructor-level reduction. Its actual native initializer,
context producer and complete observer associations are still open P data;
no native installation or deployed premise removal is claimed.

## Source admission before / retained after

Use `selected w := SourceSelectionContract.selectedRecord d x w`. The exact
original four fields are:

```lean
compile_call : ∀ w, run (selected w) = ok (.Ok (selected w).compiled)
words : ∀ w records, newRecords (selected w) = ok records →
  WitnessOk (wordWitness records.w)
publicCorr : ∀ w records, newRecords (selected w) = ok records →
  PubCorr (wordPublic records.p)
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (selected w))))
admission : ∀ w records, newRecords (selected w) = ok records →
  BuilderSpendRelation.RspendPlus
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (selected w))))
    (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness records.w)))
```

`row_call : ∀ j, endpointHonest.transport j = PV_Src_Transport.row j` is already
proved by InstalledTransport.endpoint_row_call; it is not added as a premise.

SelectedSourceReduction prepares derivation of words/publicCorr only under
these exact additional installation joins, each explicitly P, currently OPEN:

```lean
actualExternal = PV_Src_FrozenInput.external
actualRecords = PV_Src_FrozenInput.records
∀ w, SourceSelectionContract.selectedRecord d x w =
  PV_Src_FrozenInput.input (canonical w)
```

Compiler success and admission remain unchanged. These joins were already
part of the source/runtime installation gap: they are exposed, not discharged
or moved into T. The sibling's owned-reference result is not an actual Records
mapper equivalence. That equivalence and the full compiler fixture success are
explicitly open in its pinned report.

## Concrete installation and release obligations, both before and after

P-runtime: supply actual Runtime and Boundary values, actual account callback,
source hash, inputs and compiled record; install native carrier/initializer,
constructor-preserving error/request/reply/time/worker interpretation and the
actual producer of the complete extracted observation. File must be the
PDict_FileCarrier.File carrier; Reply must be PDict_World244.Reply. Arbitrary
free types or a chosen observation list do not prove these associations.

P-release: associate the same installed values with pinned release source,
compiler/flags/binary/CPU and replay the coherent dependency closure and
axioms audit. Neither an equality between generic records nor cached import
success certifies this release association.

Transfer and withdrawal: each must exhibit the same concrete runtime/boundary
and all remaining P fields on its fixture fibre, with T hypothetical. Both
remain OPEN. The historical generic T model and canonical-fibre inhabitance
do not prove this conjunction.

T has exactly its original three fields. No A/B availability or public-failure
repair is adopted; no failure is silently deleted from the observer or bad event.

## Additional symbolic source-root preparation

The root-table join is still OPEN. RootLoop prepares the actual extracted
loop's termination/index/write proof from an initial-parent equality and a
uniform successor-parent equality. RootCanonical then prepares those
instances from the already proved FIELD table recurrence plus this exact
SOURCE obligation (not a new trust assumption):

```lean
ParentRefinement : Prop :=
  ∀ a b : Digest, Canon8 a → Canon8 b →
    ∃ out, format.pool_v1_tree_parent a b = ok out ∧ Canon8 out ∧
      model out = R0P.nodeCompress (model a) (model b)
```

Here Digest is the actual forest extraction's Array U32 8, model casts its
eight raw words into ZMod 2147483647, and the ExternalLinear dictionary is
kept explicit. Source totality/canonical output/refinement must be proved for
the SAME selected dictionary. The fixed field-table certificates alone prove
none of those source properties. All these new statements are still drafts.
