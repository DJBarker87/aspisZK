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
