# Selected ordered queries into the constructed norm-buffer model

Research base: `e90e7338656f221c9a1bbde90d533ba94d002014`, branch
`research/v8-no-work-100-20260907`. The worktree was clean at inspection.
Concurrent work is preserved. No prior checked leaf or runtime source was edited.

## Endpoint and relevance

The preceding [norm-buffer proof](line-norm-buffer-review.md) starts from a list
of typed unit-circle points. The [queried residual proof](queried-pole-review.md)
instead starts from an ordered array of selected fibre indices. This leaf joins
those two interfaces using the retained V7 stored-domain definitions.

The kernel-checked endpoint is:

```text
inverseLines d.a d.b d.c (points queries) = some out
  -> exactFinalLinear final (queries i) - sourceFold d received queries out alpha i
     = PostQueryFunctional.residual final orderedPoints virtualFold i.
```

Here `points queries` is constructed from the actual
`storedInitialFibrePoint20 (queries i)`; its circle invariant is inherited from
that proved point, not supplied separately. `received` is arbitrary, and
`out` is the actual result of the constructed shared-inverse model. No global
polynomiality, image condition, buffer equality or reciprocal equality is a
premise.

This is a deterministic representation/refinement result. It does not bound
the probability of scalar acceptance or claim that an accepted proof exposes a
payment witness.

## Exact ordered interfaces

| Interface | Construction |
|---|---|
| Typed point | Slot-zero `storedInitialFibrePoint20 index`, with its intrinsic circle proof |
| Base-to-QM31 scaling | Exact tower multiplication agrees with the componentwise mixed product |
| Four denominators | `(++,+−,−−,−+)`, agreeing with `QueriedResidual.sourceDenom` |
| Flat denominator index | `4*queryOrdinal + slot`, derived by symbolic block flattening |
| Base inverse input index | `2*queryOrdinal + 0/1` for `2*x, 2*y` |
| Norm-buffer output | Existing `LineNormBuffer.inverseLines_eq_checked`, instantiated on those same points |
| Residual sign | Claimed final evaluation minus the normalized received quotient fold |
| Queried pole | Model returns `none`, not a small-probability event |

Queries need not be distinct for these identities. They preserve arbitrary
ordered arrays, including repetitions; the fresh distinct-sampling law is a
separate probabilistic interface. No sorted Merkle authentication order is used
to reindex the arithmetic arrays.

The source still has its q22 cap and canonical/index/shape checks. This leaf's
generic-q algebra does not assert the same error enum for an over-cap call. The
selected-domain coordinates are nonzero by reused V7 liveness theorems, which
matches the source's early zero-coordinate rejection guard.

## Reused proofs and remaining source boundary

The new proof consumes the exact V7 circle domain, `exactCircleX/Y`, the
retained tower field, `storedInitialFibrePoint20`, canonical coordinate
liveness, and the existing quotient/fold residual adapter. The flattening
argument is symbolic in the array and block lengths; it neither enumerates the
262,144 fibres nor unfolds a stored generator recurrence.

Still separate are:

- The executable selected-point lookup tables/window calculation and their
  mutable Rust/compiled-machine connection to the exact stored-domain model.
- Parsing/canonicality, memory/index bounds and concrete error handling.
- Authentication, actual replay/rewinding and coupling parsed C1/C2 values to
  the arbitrary received-word argument.
- The actual full-verifier/Fiat–Shamir, hiding and payment-extraction theorem.

A successful field/list model is not labeled a translated Rust proof.

## Check status and budget

The focused `SelectedQueryBuffer.lean` v2 build passed: exit 0, 24.95 seconds
Lean wall time, 5,708,742,656 bytes peak RSS, zero swaps. All ten audited
declarations use only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; the generic block-flattening lemma needs only `propext` and
`Quot.sound`. No `sorry` or new axiom is retained.

The source hash is
`7576e1831eabc70dd46aff7f34ca1f9db0ba093a103e8d17fe9a6f4d943c7022`;
the checked olean hash is
`9788388ebd1bd6382f234825739077baaff61dc0a5916578d8161adecffb04cd`.
The runner checked all imported source/olean hashes before and after the job;
they were unchanged. Borrowed source is pinned at
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, with Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` and Lean 4.32.0. Concurrent cache
HEAD advanced from `e674314c6d062377f29df84f3c4c94d4ebd7572d` in v1 to
`c7347eefcf767c375040f8f73160995a7886e3ae` in v2; neither moving HEAD replaced
the per-source pinned checks.

The retained v1 failure log records local simplification/namespace errors and
an overly broad `congr` step which tried to unfold the concrete domain. The
replacement uses a typed equality of `Fin 4` functions under `List.ofFn`, plus
symbolic list block composition. No resource cap was increased and no large
domain was enumerated. v1 exited 1 after 41.41 seconds, with 5,490,409,472 bytes
peak RSS and zero swaps; it is not claimed proof evidence.

Reproduce only when a changed dependency or missing artifact warrants it, using
a fresh log path:

```sh
EX=docs/research/v8-no-work-100-20260907/experiments
bash "$EX/run_selected_query_buffer.sh" SelectedQueryBuffer "$EX/selected-query-buffer-recheck.log"
```

The runner uses cached dependencies, `-M7000`, and an independent aggregate
process-tree RSS guard at 7 GiB. The job was explicitly serialized with the
other agents' builds. Exact log/source hashes and scope are in
[`selected-query-buffer-evidence.json`](selected-query-buffer-evidence.json).
These measurements describe Lean compilation, not proof generation or verifier
execution.

The proof body remains 40,282 bytes. There are no new proof values, challenges,
rounds, probabilistic error terms or source operations. This task performs no
SBF, prover or runtime benchmark, and makes no new CU-parity claim.

The narrow next interface after this bridge is the canonical parsed/query-table
execution coupling, not another root-count or sampling theorem.
