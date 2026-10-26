# V152–V154 source identification campaign

Branch: codex/pv-srcid-20261026. Base: research. Budget: 100 Lean
compilations and 15 Kani runs; Env-J IDs 22550–22799. No implementation
changes are authorized here. Target not yet established.

## Statement audit

`BuilderSource.SourceIdentification source toInstance` requires:

* V152: `∀ w, source.public w = BuilderSource.prover.public (toInstance w)`.
* V153: `∀ w, source.build w = BuilderSource.prover.build (toInstance w)`.
* V154: `source.transport = BuilderSource.π`.

The canonical prover's domain is `BuilderCanonical.Instance`, the subtype of
M31 public/witness pairs satisfying the lifted `RspendPlus`. Its public map
is `SpendWitnessMap.mapPub`; its trace is `BuilderRefinement.mergedTrace` on
`rustWitness`/`rustPublic`; its transport is D18 `rowEquiv`.

`PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises` is the model-scoped
consumer; it already supplies canonical `BuilderPremises`. Native association
is independent, as the recount explicitly records. Constructing a reflexive
certificate for that model alone removes none of V152–V154.

## Source boundaries

D188 accepts Charon/Aeneas as source semantics. `BuilderPublicExtracted`
extracts the actual transfer and withdrawal public projections.
`BuilderBankExtracted` extracts `parts` and `merged_banks`; `BuilderColumnsExtracted`
extracts the column wrapper. `BuilderPartsComplete.banks_columns` already
identifies successful Parts output with canonical cells. Its success guard
will first be discharged symbolically, without evaluating any concrete hash.

The forest entry port `BuilderForestAdmissionPort` retains `ExternalLinear`
and `Records` callbacks. The owned record reference has a separate P6 route;
`BuilderTransportExtracted` is an arithmetic reference, not the shipped
`Variant::coefficients` extraction. Missing associations must remain explicit
named premises, not definitions of correctness or new trust assumptions.

## Validation

Focused new modules only, shared launcher with Lean -M7000 and 6G/8G/swap0,
TasksMax128 under lead ruling (b). No existing proved modules or sibling
worktrees will be edited. Receipts will record revision, module/source and
dependency hashes, exit, wall time, peak RSS, swaps and full axiom output.

Reservation preflights 22550 (12:43:05 UTC) and 22551 (12:43:56 UTC)
were denied before scp or launcher invocation; zero Lean attempts. The second
read-only check was made too soon to be the required three-minute retry;
it is retained as an early inventory check, not a launch. The next retry is
no earlier than 12:46:56 UTC. Both denial logs and full inventories are retained.

## Capacity relaunch 1 (2026-10-26)

Recovered commits 1508d64ce5 and 71d9b75ad4. Four charged Lean attempts
(22552, 22555, 22556, 22558), all failed in PartsTotal; no Kani run.
IDs 22550, 22551, 22553, 22554, 22557, 22559 and 22560 were reservation
preflights only. Remaining budget: 96 Lean / 15 Kani. 22560 refused at
13:04:18 UTC: reserved 51,942,260,736 bytes, projected 60,532,195,328
above safe 59,055,800,320. Next retry no earlier than 13:07:18 UTC,
using 22561. Source snapshot 22559 already replaces the failing concrete
wrapping-arithmetic decisions with symbolic umul/uadd equations.

The recovered new modules other than PartsTotal are UNCOMPILED WIP.
Failed outputs containing sorryAx are diagnostic error recovery, not accepted
proofs. No such output is accepted as closure evidence.

## Resumed statement work (pending compilation)

`PV_Src_Public.output` now executes `run` (the two extracted public calls);
`output_eq` uses unconditional `run_success` to remove its fallback. It no
longer substitutes the expected public projection as the input prover's public
function. The trace executes `merged_banks` and `columns`; `run_exact` is meant
to prove its fallback unreachable for every raw bank record, not merely fixtures.

`PV_Src_OptionShape.reflect/canonical` derive the option shape from RspendPlus;
the extra option-shape field was removed from the new canonical input carrier.
The explicit `nextPairIndex < 2^64` representation bound remains: the adopted
Rspend/AppendBinding model itself has no U64 bound. This is a source carrier
restriction, not a proof that all mathematical instances have machine encodings.

The four exact remaining generic stage premises in
`PV_Src_Identification.PV_Src_Premises` are:

1. `words : ∀ i, WitnessOk (wordWitness (inputs i).witnessRecord)`.
2. `publicCorr : ∀ i, PubCorr (wordPublic (inputs i).publicRecord)
   (mapPub (K := K) (PV_Src_Public.canonicalPublic (inputs i).publicInput))`.
3. `admission : ∀ i, BuilderSpendRelation.RspendPlus
   (mapPub (K := K) (PV_Src_Public.canonicalPublic (inputs i).publicInput))
   (BuilderCanonical.liftWitness
     (BuilderRecordCanonical.witness (wordWitness (inputs i).witnessRecord)))`.
4. `row_call : ∀ j, transport j = PV_Src_Transport.row j`.

The encoded canonical family is intended to construct all four, using admitted
canonical relation data, raw-word encoding theorems, and the extracted arithmetic
row reference. This is not a construction of the opaque forest `Records` callback
or a proof that successful forest admission implies RspendPlus. These native
associations remain independent of the stage theorem. V154 additionally retains
the existing P6 Kani connection from shipped S2 to the extracted row reference;
its receipt is reused, not introduced as a new Lean axiom or rerun unchanged.

`PV_Src_Consumer.of_identification` targets the exact original
`PrivacyR1Headline.BuilderPremises` type. The existing
`PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises` is a proved fixed-input
model theorem, with no SourceIdentification argument. Compatibility with its
contract does not install the new input into the deployed RunJoin endpoint.

Reservation refusals 22561 (13:07:26), 22562 (13:10:45), 22563 (13:14:02)
are zero charged Lean attempts and have individual full inventory receipts.

`transport-reuse.json` compares the historical receipt's file pins. The actual
shipped `transport.rs` is byte-identical. The reference crate acquired other
modules and dependencies since that receipt; no claim of an unchanged full
crate build is made. The new test-only `tools/pv-srcid/transport-kani/` harness
calls actual `Variant::S2.coefficients` on 1024 arbitrary four-word cells and
checks an arbitrary in-range output against `row_arithmetic`. It has no stubs,
unwind 1025 with unwinding assertions, and is NOT RUN yet. Cargo metadata
validated its dependency paths locally; no compilation or target directory
was created. If run, expected time is Kani compilation followed by symbolic
array-copy aggregation/solver, not native finite-field arithmetic. It must use
its own sole 6G/8G/swap0/TasksMax64 scope after a successful reservation.

## Validated stage progress after capacity returned

22567 PartsTotal passed: 2.83 s, 4,109,796 KiB peak RSS, zero swaps.
22568 Trace passed; 22569 Public passed; 22570 Transport passed;
22571 Identification passed; 22572 Records passed. All printed axioms are
subsets of propext/Classical.choice/Quot.sound. Exact receipts and source
snapshots are in attempts.jsonl and out/time/sha logs. No full replay ran.
22573 PublicRecords failed at the frontier-array and scalar-index roundtrip;
the replacement adds arr20_getF and UScalar.ofNatCore_val_eq to its restricted
simp set. The failed output is retained and is not accepted as a proof.
22574 and 22575 reservation preflights were refused. 22575 was an early
inventory check, 177.6 seconds after 22574 rather than the required 180;
it ran no compile and is not treated as the scheduled retry. Next launch
uses fresh ID 22576 no earlier than 13:35:29 UTC. Charged budget 11/100;
Kani 0/15. No implementation change under crates/ or programs/.

## Direct forest proof port (uncompiled)

The generator forest_proofs.py ports 24 existing symbolic proof modules to
BuilderForestAdmissionPort, changing import/module/namespace identifiers only.
It does not emit a broad normalization proof of duplicate source semantics.
forest-proof-provenance.json records each original/output SHA-256. Separate
ForestPartsTotal/ForestTrace/ForestIdentification modules apply the new proofs
to the forest port's actual Parts/banks/columns definitions. ForestRecords
preserves all raw fields across nominal carriers; ForestCanonical constructs
the certificate on the same canonical encoding carrier. Fixtures and Consumer
are now intended to use this direct forest source chain as well. These newer
modules still need focused validation; none is presently a closure receipt.
ForestBanks identifies successful CopyRecords.banks.merged with ForestTrace.run.

## Direct forest validation, 14:14 UTC

Forest BankMerge22588, PrimitiveWriters22590, PrimitiveArguments22591,
Inverse22599, InverseResult22600, PrimitiveDigests22601 passed with standard
axioms and zero swaps. The fixed-prime inverse specialization is permanent
in the generator, using `multiply_prime` over literal ZMod2147483647 and the
actual source divisor cast. Failed 22592/22593/22595 are retained; the
replacement never evaluates the concrete exponent.

22602 DigestArguments found that the forest's std aliases live in the imported
BuilderForestStdPort namespace, unlike the aggregate extraction's local ones.
The generator now maps these explicit prefixes too; ForestPartsTotal's map
prefix was corrected likewise. The failed output's sorryAx lines are error
recovery and NOT accepted evidence. Queue resumes at22603; charged attempts
remain counted solely from attempts.jsonl. All reservation-only IDs remain
zero charged attempts.

PV_Src_NativeInput is a new UNCOMPILED data adapter for the actual returned
forest compilation/public statement. It does not hide run success in its
input domain. Transfer/withdrawal requests choose recipient/out-value as the
source wrappers do; public transition comes from the compiler's returned
payload. A native-output certificate, if completed, must expose compile_call,
words, publicCorr, admission and row_call as named premises, and must prove
raw trace equality through returned_bank rather than assume it.
