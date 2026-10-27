# Statement comparison and retained native obligations

No endpoint or existing theorem is edited. No ledger row is yet removed.
Target not yet established.

| Row | Before, exactly | New candidate conclusion | Remaining source issue |
|---|---|---|---|
| V152 | `∀ w, source.public w = BuilderSource.prover.public (toInstance w)` | `PV_Src_Identification.public_eq`, same equation for `prover inputs transport` | Source public calls are extracted; the same record/public/admitted canonical instance must still be supplied by the enclosing forest run. |
| V153 | `∀ w, source.build w = BuilderSource.prover.build (toInstance w)` | `PV_Src_Identification.build_eq`, same equation for actual `merged_banks`/`columns` stages | `words`, `publicCorr`, `admission`; association of the forest result and its opaque `Records` callback with those bank inputs remains. |
| V154 | `source.transport = BuilderSource.π` | `PV_Src_Identification.transport_eq`, same equivalence equality | `row_call` associates chosen source transport with the extracted arithmetic reference. Historical unstubbed native S2 row certificate is separate P6 evidence; new coefficient-wrapper harness is unrun. |

The `prover` definition contains data/computations only. No correctness equation,
spend relation, trace validity, or SourceIdentification defines its output. Its
public and trace fallbacks are intended to be proved unreachable by unconditional
success theorems. The target map `toInstance` uses the named `admission` proof;
this necessity is not erased or hidden in the source definition.

For the canonical encoded family, `PV_Src_Canonical.premises` constructs all four
fields, from canonical witness/public encodings and the canonical instance's
original RspendPlus property. Its carrier retains `indexBound : nextPairIndex <
2^64` and arbitrary context bytes. Option shape is derived from the original
relation by `PV_Src_OptionShape.canonical`, not assumed anew. This is a general
encoding theorem, not a proof that the source compiler admits every mathematical
canonical instance. In particular RspendPlus itself has no U64 index bound.

`PV_Src_Fixtures` reuses canonical fixture fibres from the sibling branch via
committed, uniformly renamed sources, with provenance hashes. Both variants
have a successful actual extracted bank/column run and matching public fibre
as *candidate* theorems. These are mathematical release-fixture fibres, not
native fixture-byte association; V047 remains distinct. The transfer change
sentinel uses the explicit round-split proof copied from that branch.

The consumer's original `BuilderPremises` type retains exactly its matching
public guard, field carrier, basis and raw-trace soundness conclusions.
`PV_Src_Consumer.of_identification` is the proposed generic application;
`extracted_stages` supplies the newly constructed certificate. The original
`PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises` is fixed to
`BuilderSource.prover` and has no certificate parameter. Its existing body and
the deployed endpoint remain unchanged; no RunJoin or operational source
installation follows from type compatibility alone.

## Validated extracted-stage result (15:10 UTC)

The direct forest certificate `PV_Src_ForestCanonical.identification` and its
public/build/transport equations passed attempt22632. `PV_Src_Consumer` passed
22644: `of_identification`, `extracted_stages`, `forest_stages`, and the exact
existing consumer contract all have standard axioms. This is compatibility
with the unchanged BuilderPremises type, not installation into the fixed
`PrivacyR1HeadlineDeployedReal` input. Neither that endpoint nor its observer,
simulator, random carriers, failure event or numerical bound is changed.

`PV_Src_NativePremises` passed22642 after the native-input reader was corrected
to the actual Fin29/Fin1024 signature (NativeInput22641; old shared object/source
snapshotted, hashes/sizes retained). The five final native premise families are:

```lean
compile_call : ∀ i, run (inputs i) = ok (.Ok (inputs i).compiled)
words : ∀ i records, newRecords (inputs i) = ok records →
  WitnessOk (wordWitness records.w)
publicCorr : ∀ i records, newRecords (inputs i) = ok records →
  PubCorr (wordPublic records.p)
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
admission : ∀ i records, newRecords (inputs i) = ok records →
  BuilderSpendRelation.RspendPlus
    (mapPub (K := K) (PV_Src_Public.canonicalPublic (publicInput (inputs i))))
    (BuilderCanonical.liftWitness
      (BuilderRecordCanonical.witness (wordWitness records.w)))
row_call : ∀ j, transport j = PV_Src_Transport.row j
```

Here `run` is the actual extracted `compile_forest_from_copies` call, with
request-selected out-value/recipient and native snapshot; `publicInput` calls
the actual extracted transfer/withdrawal projection with the returned compiler
public statement's transition. `newRecords` is the actual constructor using
the same arguments and Records dictionary. ExternalLinear/Records are existing
source-port parameters, not new Lean axioms or discharged native associations.
The source prover reads the returned `compiled.semantic_c1.c1`, not a canonical
trace substituted into its definition. The unfinished native certificate must
obtain its internal record/bank from that same execution. No raw_trace_eq field
is assumed. Its compiler-return theorem remains pending validation.

These are FIVE named families, not a claim that only five atomic native laws
remain: WitnessOk retains values/bits/siblings; PubCorr retains its seven fields;
RspendPlus retains the original spend relation plus sentinel. These definitions
will be printed in the final audit so their conjunction leaves remain visible.
No native V152–V154 deployment row has yet been removed from the ledger.

## Authoritative native result after attempts22675–22687

For all three rows the before and after conclusions are **identical**:

| Row | Native theorem (namespace `R1Z.PV_Src_NativeIdentification`) | Status |
|---|---|---|
| V152 | `public_eq p i : (prover inputs transport).public i = BuilderSource.prover.public (toInstance p i)` | REDUCED to the five named families and existing source-port parameters |
| V153 | `build_eq p i : (prover inputs transport).build i = BuilderSource.prover.build (toInstance p i)` | REDUCED; actual returned compiler columns, not a substituted model trace |
| V154 | `transport_eq p : (prover inputs transport).transport = BuilderSource.π` | REDUCED; native transport association remains `row_call` |

`identification` constructs the original three-field structure. Receipt22676
prints standard axioms for every declaration. The successful-run premise retains
both Result layers, every original compiler check, and the same returned payload.
`ForestCompilation.returned_bank`22675 discharges the internal record-to-returned-
bank association. It does not assume this equality as a new premise.

`NativeConsumer.builder_premises` and `phased_builder_premises`22677 accept the
constructed instance with the unchanged original consumer type. The fixed
`PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises` remains its existing
model theorem. No source, observer, simulator, failure event or deployed endpoint
is edited. No native ledger row is removed.

The five `PV_Src_Premises` families printed above are retained, not discharged or
renamed as cryptographic assumptions. `WitnessOk` has three fields (values is a
triple conjunction); `PubCorr` has seven. `RspendPlus` contains the original
`Rspend` and transfer change-sentinel obligation. The existing `ExternalLinear`
and `Records` source-port dictionaries are also explicit parameters. Their
concrete native association is not proved by the standard-axiom audit.

Both release canonical fibres are inhabited (`Fixtures.fibres`,22662), with
actual extracted bank/column stage success and equal public fields. The generic
canonical encoded certificate is constructed (`ForestCanonical.identification`,
22632). **Full native fixture non-vacuity remains OPEN**: no witness for the five
native premise families for either release fixture has been constructed, nor has
V047 native fixture-byte association. Thus these inhabitance results do not
establish native `compile_call` satisfiability.

Additional local native helpers: `NativeValueBits.helper/cells/bit_boolean`22682,
`NativeValueReconstruction.reconstruct`22683 and
`NativeDirections.closure_result/run_eq/booleans`22687. These prove actual local
source behavior without a compiler-success premise. They do not discharge all
`WitnessOk`/`PubCorr` or opaque record-callee associations.
