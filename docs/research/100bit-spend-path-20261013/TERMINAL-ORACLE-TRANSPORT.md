# Reusing the decoder with terminal oracle reads

The existing 33-row decoder proof now applies when the verifier's final
decision is an oracle program rather than a pure Boolean. The added reads
remain in the same prover–verifier experiment and its query bound. This
is a checked interface and decoder transport result; the concrete Rust
terminal decision and complete knowledge/privacy argument remain separate.

## Exact extension of the existing experiment

`UnifiedOracleVerifier.verifier` uses the existing generic `OracleVerifier`
with the unchanged unified protocol. A terminal program returning a Boolean
without queries specializes exactly to the old verifier. The wrapper still
reads every sampler chain's first cell.

`UnifiedOracleTrace.trace_decomposition` proves:

```
full experiment trace = old experiment trace with decision=true
                        ++ actual terminal decision trace.
```

The proof reuses `FS2.experiment_eval`, the old `FS2.verifier_eval`, and
the oracle-verifier evaluation theorem. The full result Boolean is the
terminal program's result. There is no assumption that terminal queries
are fresh or disjoint from earlier queries.

`TraceAppend` proves that a previously read address has the same
`tableBefore` after a suffix is appended, and that its `traceFrom` gains
exactly that suffix. Distinct first-read counts only increase; a bad
first-read event in the prefix persists in the whole trace.
`FollowAppend` proves that a successfully completed ordinary or background
sampler remains completed with the same output after any suffix.

## The 33 decoder cases are reused once

`UnifiedOracleTotalCase.decodes_and_follows` derives membership of each
chain's first address in the old trace. It transfers the full-trace read
bound and absence of the existing hash events to that prefix, then invokes
`UnifiedTotalCase.decodes_and_follows` once. The append lemmas transfer its
decoded table and completed sampler to the full trace. None of the initial,
semantic, reseed, opening, query, or rho cases is re-proved.

`UnifiedOracleInj.inj` packages that result into the existing `Inj3`
interface. Its event is `CombinedMerkleCollision.Coll`, with the already
checked `12*Qtot^2/2^256` mass bound. It obtains the old event exclusions
through `CombinedMerkleCollision.old_included`. The additional Merkle
events remain available to the [causal recovery proof](CAUSAL-COMMITMENT-STABILITY.md).

The retained premises include the public byte length, all 33 label values,
the fixed codec's empty-record representative, and a distinct-read bound
on the **whole** experiment for every oracle. The terminal program and
extractor remain parameters. Neither this adapter nor its collision budget
supplies D1, D2, D3, an efficient extractor, a numerical security claim,
or a privacy simulator.

## Reproducible module names and evidence

The pinned workspace has mixed historical module names. The bundle records
the actual importable names explicitly rather than assuming an `R1` prefix:

| Local source | Compiled module |
|---|---|
| `UnifiedOracleVerifier.lean` | `UnifiedOracleVerifier` |
| `TraceAppend.lean` | `TraceAppend` |
| `FollowAppend.lean` | `R1FollowAppend` |
| `UnifiedOracleTrace.lean` | `UnifiedOracleTrace` |
| `UnifiedOracleTotalCase.lean` | `UnifiedOracleTotalCase` |
| `UnifiedOracleInj.lean` | `R1UnifiedOracleInj` |
| `TerminalOracleCheckpoint.lean` | `R1TerminalOracleCheckpoint` |

The evidence bundle's packaging base is
`0e8451fed132773faa356fe305844474bb0e21d9`. Its components were developed
against the preceding base and the exact causal sources now committed there;
source snapshots and imports identify those bytes. The final checkpoint
exited 0 in 1.48 seconds with 3,537,416 KiB peak RSS and zero swap, under
4G/6G/zero-swap limits. Its source SHA-256 is
`da8bdfe076153caf7f3a30b4c71dac399d7aaa31c8364e5438e301c0cd7b9669`.
All thirteen reports use only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

`evidence/lean-terminal-oracle-20261014/` retains the exact successful and
failed source snapshots, receipts, logs, module/object mapping, runner pins,
and deterministic object archive. The older failed target
`R1UnifiedOracleVerifier-a` is distinct from the successful unprefixed target;
the failed target has no archived final object.
