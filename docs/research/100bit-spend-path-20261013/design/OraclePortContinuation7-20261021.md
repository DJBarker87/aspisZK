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

Pending composition and focused verification.

## Stage 3: premise and numeric comparison

Pending final signature audit.

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
