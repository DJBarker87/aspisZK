# V152 admission boundary

Entry HEAD b3ad0edf5b43d879f7b36abffdcb2d2fd30d0213, branch codex/pv-runjoin-20261026, exact worktree /Users/dominic/ZK/.worktrees/pv-runjoin.

Recount 6 (lead-provided current ledger): **407 rows; OPEN 86; CLOSED-ON-CANDIDATE 44**. No closure is inferred from the merge itself.

For a fixed source : HonestProver K and toInstance : source.Instance → BuilderCanonical.Instance, SourceIdentification requires:

- V152: ∀ w : source.Instance, source.public w = BuilderSource.prover.public (toInstance w).
- V153: ∀ w : source.Instance, source.build w = BuilderSource.prover.build (toInstance w).
- V154: source.transport = BuilderSource.π, equality of the full Fin 1024 equivalences.

The concrete source PV_Src_NativeIdentification.prover inputs transport has Instance := I. Nothing in this carrier constrains inputs : I → Input. In particular I := Input and inputs := id are valid, and Input is a raw structure with caller-supplied compiled data. A w of that source.Instance does not carry semantic Admission.

The candidate `PV_RunJoin_AdmissionBoundary23.bad` is fully explicit: the recorded withdrawal public record with amount 1, the original fixture input witness with pair.value 0, withdrawal change with value 0, original lane anchor/snapshot and original transfer compiled payload. Its three reconstructed values are 0,1,0. The relation requires the impossible natural-number equation 0 = 1 + 0. Checked in attempt 38115, exit 0, standard axioms only (propext, Classical.choice, Quot.sound); receipt-38115.json records timing, RSS, swap, exact revision/blob and dependency fingerprint. `source_instance_not_admitted` types the same explicit bad value as the exact raw prover Instance, and `admission_not_derivable` refutes the universal derivation. This is a counterexample to deriving UniversalBuild22.Admission from membership of the raw source carrier; it is not a counterexample to V152, which takes a particular source and canonical map and cannot be refuted by choosing an unadmitted raw tuple alone.

V152 therefore still needs a proof ∀ i, Admission (inputs i) for the chosen raw family before UniversalBuild22.toInstance/public_eq can instantiate its canonical map; alternatively a separately stated admitted subtype supplies that proof in its carrier. Changing to that subtype changes the source domain and is not a closure of the raw-family statement. The public projection computation itself is unconditional (UniversalPublic22); existence of its canonical admitted witness is the missing boundary. No V152 removal claimed.
