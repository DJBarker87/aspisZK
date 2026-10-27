# Exact checked statements (local notation is defined in each linked source)


## PV_RunJoin_OsFailureEndpoint

Full binder/notation context: `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_OsFailureEndpoint.lean`.

```lean
theorem PV_RunJoin_OsFailure
    (adv : (rust).Adversary) (w : (h).Instance) (r : World)
    (fault : PV_RunJoin_OsFailure.FirstDrawFailure runtime r)
    (old : ∀ i, ¬ oldBad w i r.coins.1.1)
    (seed_safe : ¬ ProverCommitSeedEvent19.seedGuess
      (queries adv w r.coins.1.1) r.coins.1.2)
    (fuel_safe : ∀ j, ¬ ProverCommitFuelJoin22.failure j r.coins.2)
    (decoded : runtime.observerOracle adv x
      (.ok (.stop .Entropy,{fault.next with provider := fault.after})) = [])
    (k : Fin 8)
    (selected : FsAbort.firstGood
      (fun o : AttemptOut K CommitHandle Aux =>
        P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB o.ch ∧
          VR1 h o.ch w ∧ o.exh = false)
      (GamesR1PBin.realOut W Pr h B outputs x w
        ((W).look r.coins.1.1.1) r.coins.1.1.2) = some k) :
    PV_RunJoin_Deployed.execute runtime h x w r =
      .ok (.stop .Entropy,{fault.next with provider := fault.after}) ∧
    (¬ ∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) ∧
    ((rust).real h B outputs adv x w r ≠
      (source).real h B outputs
        (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1)
```


## PV_RunJoin_SourceFailureIndependence

Full binder/notation context: `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_SourceFailureIndependence.lean`.

```lean
theorem source_witness_independent {S W : Type}
    (account : ProverRwEffectCallback.Account S) (state next : S)
    (nonce : Array U8 32#usize)
    (called : account.call_mut state 0#usize = .ok (nonce,next))
    (entered : aspis_prover.state_only_entropy.entropy_nonzero32 nonce = .ok true)
    (input : Slice U8) (back : Back) (hprefix : before = .ok (input,back))
    (err : getrandom.error.Error) (written : Slice U8)
    (fault : getrandom.fill input = .ok (.Err err,written))
    (mapped : core.result.Result.map_err
      (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError account)
      (.Err (.Os err) : Status) () = .ok (.Err .Entropy))
    (variant : core.cmp.PartialEq.ne.trait_default
      transport.Variant.Insts.CoreCmpPartialEqVariant .S2 .S2 = .ok false)
    (pub : W → Pub) (compiled : W → Compiled) (hash : W → Hash)
    (store : Store) (w u : W) :
    RealR1_client.prove_for_proof_accounts account (pub w) (compiled w) (hash w) store state =
      .ok (.Err .Entropy,store) ∧
    RealR1_client.prove_for_proof_accounts account (pub w) (compiled w) (hash w) store state =
      RealR1_client.prove_for_proof_accounts account (pub u) (compiled u) (hash u) store state
```


## PV_RunJoin_AvailableOption

Full binder/notation context: `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_AvailableOption.lean`.

```lean
theorem privacy_headline_from_premises_available :
    OsAvailable template outputs x runtime boundary →
    PV_RunJoin_Endpoint.PV_RunJoin_Premises template outputs x runtime boundary →
    (∀ (adv : (rust).Adversary) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTest h B outputs rust adv x w) -
        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
          (simE (h).transport B outputs x))| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```


## PV_RunJoin_PublicFailureEndpoint

Full binder/notation context: `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PublicFailureEndpoint.lean`.

```lean
theorem privacy_headline_public_failure
    (premises : PV_RunJoin_Endpoint.PV_RunJoin_Premises template outputs x runtime boundary)
    (signal : Option E) (adv : (rust).Adversary)
    (w : (h).Instance) (hw : (h).public w = x.1) :
    |mean (fun r => bit ((rust).observe adv
      (real template outputs x runtime failure signal adv w r))) -
     mean (fun i => bit ((rust).observe adv
      (ideal template outputs x runtime failure signal adv i)))| ≤
      modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
        QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1) +
        2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge
```
