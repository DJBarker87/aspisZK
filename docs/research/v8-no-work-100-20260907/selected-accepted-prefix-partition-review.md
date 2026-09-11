# Checked accepted-prefix partition; concrete source refinement remains open

`experiments/SelectedAcceptedPrefixPartitionV2.lean` is kernel-checked: one
retained target, five standard-only axiom audits. It partitions the **existing
selected ideal compact-field acceptance predicate**, not the return value of
the Rust verifier. It neither assumes nor proves `acceptance → HighPrefix`.
The exact source-to-ideal constructor described below remains the endpoint.
No gamma count, suffix probability, payment extraction or Fiat–Shamir claim is
added by this leaf.

## Exact deterministic result

The namespace is `AspisV8.SelectedAcceptedPrefixPartition`; import the **V2**
file, not the failed predecessor (both contain the same namespace). Its only
direct import is the checked `SelectedMiddleGammaCover`.

Write `g`, `f`, `h`, `s` for the existing `goodPrefix`, `factorPrefix`,
`higherPrefix`, `SelectedHigherYHighSupport.HighPrefix` of one execution and
one `(gamma,kappa,tau,alpha)` prefix. Existing implications and the new thin
`higher_implies_factor` establish `s → h → f → g`. The five branches are:

| Branch | Exact predicate | Interpretation / retained obligation |
|---|---|---|
| `noGood` | `¬g` | No good representative; not silently called high support. |
| `noFactor` | `g ∧ ¬f` | Good representative outside the retained-factor event; existing interpolation/OOD exceptions remain. |
| `lower` | `f ∧ ¬h` | Non-higher factor-event branch; not itself an assertion of degree exactly one or two. |
| `low` | `h ∧ ¬s` | Higher event without any high witness; not merely existence of a low-support witness. |
| `high` | `s` | An actual same-Q witness satisfying the checked high-support condition. |

`unique_branch` proves mutual exclusivity and exhaustiveness.
`accepted_partition` proves, for the same ordered queries, rho and later
challenges, exactly

```text
idealAccepts(e, gamma, kappa, tau, alpha, queries, rho, later)
  ↔ ∃! branch,
      idealAccepts(e, gamma, kappa, tau, alpha, queries, rho, later)
      ∧ prefixCase(e, gamma, kappa, tau, alpha, branch).
```

`idealAccepts` is the existing `CausalOrderedRelation.accepts` using the actual
constructed rows, `oracle 0 (e.raw gamma)`, and `e.strategy gamma kappa`.
It is not a placeholder equality to a Rust return value. All five events
retain the same suffix; no extra suffix repair is charged here. Q may be
chosen after alpha, as may the actual final256. No Q is moved before alpha.

`no_good_cases` refines the first branch into an off-family final,
a nonzero first-fold prior, or an actual `firstCollision` for a member of the
bad literal family. This is an inclusive alternative, not another disjoint
partition, and `firstCollision` is an algebraic collision of the first-response
error polynomial, **not** a Merkle-hash collision. It does not need terminal
acceptance. It reuses `mem_literalFamily` and `prior_at_fold`; no pointwise
elimination of these cases or probability estimate is asserted.

`high_same_quotient` extracts **one and the same** `Q` with:

- the existing `Witness`: literal family membership, no bad anchor, actual
  final equal to `coefficientFoldLayer 256 alpha Q`, and the old retained
  higher-factor root;
- image equations `Q 1023 = 0` and `b*Q 1022 - c*Q 1021 = 0`;
- all four actual original row errors zero;
- `200808 ≤ fibreCount (e.raw gamma) Q`, derived from
  `full_bad_partition` and `HighSupport`, since
  `262144 - 4*15334 = 200808`.

Thus the existing `SelectedMiddleGammaCover.high_prefix_mem` / selected cover
can consume the high branch. This theorem does not infer that threshold from
acceptance or 22 sampled queries. Literal-family coverage alone starts at
9558 full fibres. The `lower` branch can be refined by the already-checked
`CausalHigherYClassification.exists_fixed_prefix_cover`: outside its higher
alternative, retain the fixed exceptional event or the actual fixed-family
tuple. A lower branch is not automatically a payment witness, and an absent
early C1 candidate does not imply a component own-support bound.

## Correct Rust caller and exact fixing boundary

The inspected path is
`performance_verifier::{verify,verify_payment} → verify_parsed → semantic →
prepare → relation`, not the old standalone
`relation_callback::verify_relation` with externally supplied ordinary inputs.
The performance caller invokes the repaired dense `prepare(..., true)` or
`structured_weights::prepare`; the unshifted regression path is excluded.

All four current files were independently compared, by SHA256 of `git show`,
with source checkpoint `9e432896a4e1515efebe940b71fd9b4f9f009189` (the executed
positive/devnet checkpoint identified by the parent). The full hashes are in
`experiments/selected-accepted-prefix-partition-evidence.json`. This task
performed source inspection, not another Rust execution, binary attestation
or account/settlement audit. Proof-source parent is separately
`2f92bdd5f08fa89060c85262a55c19545a002064`.

| Rust boundary | Literal data / check | Existing Lean interface and precise remaining seam |
|---|---|---|
| `relation_callback.rs:86`, `parse` | 697 canonical QM31 fields; two 26-byte roots; 24 nonce bytes; 22 records of 621 bytes; equal-size frontiers; body 24890..40282 bytes with the stated divisibility check. | `CanonicalRelationInput.parse_success`, `decoded_boundary` fix field/response/final offsets for its typed parser. They do not translate this entire `Wire`, packed-record decoding and byte-error control flow. |
| `performance_verifier.rs:33`, `semantic` | C1 root before lambda/chi; C2 root afterwards; ten compact semantic rounds, each absorbed before its challenge. The selected terminal uses the exact 3×28 projection from 3×29 claims, skipping lane 28 of each row. | Fix C1 first and allow C2 to depend on lambda/chi. A successful aggregate semantic terminal is not an individual-row certificate. No new semantic extraction assertion here. |
| `inactive_row_binding.rs:53`, `points_absorb` / `to_gamma` | Absorb all 3×29 ordinary claims at fields 271..357. Draw OOD point0, absorb its 29 answers at 359..387, then draw point1 with at most three distinctness attempts and absorb 388..416. Only then absorb batching nonce and draw nonzero gamma. | `OODInterpolant.Data` and `Execution.data/claims` model these fixed objects after the sequential OOD prefix and before gamma. OOD point1 may depend on the first answer; it is not an independent simultaneous point draw. Helper degree two does not change 29-component claim-error degree at most 28. |
| Dense `inactive_row_binding.rs:129` or structured `structured_weights.rs:136`, `prepare` | Field358 inactive claim is absorbed after gamma, before nonzero kappa. The actual functional is the fixed inactive mask plus three MLE rows with scales kappa,kappa²,kappa³. Ordinary claims use the same scalars and gamma powers. | `Execution.weights` has four fixed covectors; `inactive : K → K` has the correct timing. `ComponentRows.source_claim` / `OODInterpolant.Data.source_prior` supply symbolic corrected-claim identities. The actual mask and MLE loop still need to be related to those four covectors by the source constructor. |
| Same `prepare` | Choose x if OOD x-coordinates differ, else y. Compute the affine interpolant, checked inverse of `h0-h1`, and chord `(a,b,c)`. Subtract intercept times functional coefficient0 and slope times coefficient2 (x) or coefficient1 (y). | `Data.Checked`, `checked_inverse_eq`, `chord_nondegenerate`, `eval_at_points`; `InterleavedChordRows.literal_transpose_dot` / `concrete_before_prior`. Successful source inversion must furnish `Data.Checked`; the ideal `Execution` does not assert it automatically. |
| End of `prepare` | Bind derived ordinary functional and corrected claim before nonzero tau. Dense path binds the dense vector; structured path binds its explicit v2 functional description including all variable inputs and the actual expanded 128 bytes of masks. | Same mathematical row functional is the target, but these are different transcript framings. The 545-byte structured description is not the old dense 16384-byte binding. Do not use a dense-path transcript equality for the selected structured path. |
| Dense `relation:155`, structured `relation:178` | Compact response0 fields417..422 before alpha0, with coefficient4 reconstructed from carried claim. Alpha0 may be zero. Final256 fields441..696 precedes the query schedule and rho. | `CanonicalRelationInput.decoded_response/decoded_final/decoded_boundary`; `CausalOrderedRelation.Strategy.firstResponse/final`. The actual final remains adaptive after alpha0. No quotient Q is sent to this verifier. |
| `relation_callback.rs:122`, `query_schedule` | Absorb final256 and final nonce, then draw an ordered 22-distinct schedule from 2^18 fibres with cap64; then nonzero rho. | `OrderedQueryGame.Schedule domain 22`. Prefix-respecting source sampling/coupling remains separate from the deterministic partition. No conditional-uniformity or FS assumption is inserted. |
| `relation_callback.rs:170`, `opened_values_prepared` | Record ordinal i belongs to query[i]. Decode C1 bytes403, C2 bytes186, salt32; sort authentication entries by query ID while retaining value order. Verify two depth18 minimal subtrees. | `MinimalMultiproofPaths.accepted_q22_paths` derives each requested sibling path and hash-call coverage from its typed success predicate. It does not itself produce unique pre-fixed total C1/C2 words or exclude hash collisions. Packed canonical values and authenticated-word provenance must be supplied by the source/authentication bridge. |
| Same openings function | Four source-ordered slots `(x,y),(x,-y),(-x,-y),(-x,y)`; subtract affine interpolant, divide by actual chord, reject zero denominators, then normalized circle-to-line fold at alpha0. | `SelectedReceivedOracle.oracle_slots/oracle_folded/query_residual` and `TupleQueryTransport.query_zero_iff` give the corresponding algebra. One alpha-fold equality is not four pointwise equalities; `FoldSupportClosure.four_matches_iff_full` requires four distinct alphas. |
| `relation_callback.rs:273`, `inject`; both relation loops | Add query functional and claim using rho^(j+1); bind increment before the three later compact responses, each before its alpha. Structured query covectors start in dimension256 and never pass through the chord or first fold. Terminal is ordinary + query + carried-image scalar. | `CausalOrderedRelation.acceptance_iff_terminal_zero` handles the constructed ideal raw rounds. The actual mutable/deferred accumulator and image-terminal recurrence still need a source refinement proof. An aggregate scalar zero does not imply each query residual, image equation or ordinary row error is zero. |

## Rejection paths versus the accepted-event partition

`verify` returns codes 1/2 for public/transition decoding and 3 for body parsing;
`verify_parsed` maps semantic failures to 4, preparation failures to 5, and
relation failures to 6. The underlying errors include canonical/shape/domain,
sampler, authentication and terminal failures. These are rejecting source
paths, not extra accepted ideal branches. The typed `verify_payment` relies
on the outer wrapper's canonical/account checks and does not establish them.

There is no separate `Error::Replay` in this callback. Transcript replay or
source-to-ideal coupling failure denotes an unmet external refinement
obligation, not a fabricated Rust status. A successful deterministic hash
replay does not imply a fresh ideal challenge law. No malformed/replay failure
probability is invented, and this report does not equate commitment binding
with total-word availability.

The minimal still-missing source theorem should consume one successful
corrected `verify_parsed` run **plus** an authenticated, fixed-total-word
interpretation (or its explicit collision alternative), construct the literal
`Execution 22` fields and a prefix-respecting `Strategy`, and derive
`idealAccepts` for the decoded same response0, final256, ordered queries, rho
and three later alphas. It must establish:

1. Literal typed parsing, QM31 arithmetic, geometry/inverse, masks/MLE weights,
   claims, chord and corrected scalar equal the constructed ideal fields.
2. The two fixed total received words agree with every authenticated packed
   opening at the actual query indices, with exact gamma batching and slot
   normalization; a finite-root commitment alone is not this premise.
3. The actual compact response/ordinary-query-image recurrence has the ideal
   terminal equality. Existing symbolic algebra can be reused instead of
   assuming a `same_prior` or `same_terminal` field.
4. Across continuations the constructor respects each absorption boundary:
   C1/C2 before OOD/gamma, inactive after gamma before kappa, response0 before
   alpha, final after alpha before queries, later responses before their
   challenges. Embedding just one transcript as a constant strategy does not
   establish this family-level property.

Once that theorem exists, the new `accepted_partition` applies directly;
there is no further acceptance-to-high-support implication to assume. The
partition deliberately does not resolve the source/authentication alternatives,
nor the later suffix or FS distribution.

## Focused check and immutable evidence

| Target / exact tag | Exit | Wall s | Peak RSS KiB | Swaps | Result |
|---|---:|---:|---:|---:|---|
| `SelectedAcceptedPrefixPartition` / `selected-accepted-prefix-partition-nuc-v1` | 1 | 3.46 | 6845272 | 0 | Field-notation errors and concrete elaboration recursion; cascading sorryAx rejected. |
| `SelectedAcceptedPrefixPartitionV2` / `selected-accepted-prefix-partition-v2-nuc-v1` | 0 | 3.65 | 6883096 | 0 | Five standard-only audits, no warnings. |

V2 repaired explicit `Branch` binders, kept `curvePrimeFactors` locally
irreducible, constructed a named `SelectedIdentityCover.Root`, and supplied
the explicit fibre dimension. No theorem premise or resource cap was raised.
Both sources and all six exact attempt source/log/manifest artifacts are
retained. The successful output is copied locally and SHA-verified; it is an
ignored cache artifact, not mandatory publication-clone data.

The five `#print axioms` results are `unique_branch`,
`higher_implies_factor`, `accepted_partition`, `no_good_cases`,
`high_same_quotient`, each using only
`propext`, `Classical.choice`, `Quot.sound`. The V1 partial audits receive no
additional target credit. Source scan found no sorry/admit/new axiom or
native_decide.

Exact green digests:

```text
source/snapshot 8298faacc822409d237df48ac12e7c7ad7853f13615f60a7757769d8de7d33b9
olean          c49c8eb10d16d3edd88b81dacc072d3fb0d85867f1939cff6b246d308b1932db
log            b50a85b88b6b54d302424d9454c6ddc0839a7be807067ccab39c6f08478149a7
manifest       a7106e6249c022dd9be26060faedd12d467d62f76cf20900b6278895e1d283eb
```

The inherited runner is pinned separately to `289d7356…`, borrowed sources
to `26a9cd47…`, Lean 4.32.0 commit `8c9756b2…`. The raw command is recorded
in each log (`lean -j1 -M9500 -R overlay -o target.olean target.lean`). Both
scopes record MemoryHigh8GiB, MemoryMax10GiB, MemorySwapMax0, CPU200%, recursion
depth200, heartbeats200000. All transfer used
`dombarker@100.108.41.90` with BatchMode, ConnectTimeout10,
StrictHostKeyChecking and `HostKeyAlias=nuc.local` for key reuse only.

The green log records 1035 registered entries unchanged before/after.
The direct imported `SelectedMiddleGammaCover` source/output pair was also
checked against both immutable manifests and local retained bytes. This is
not a fresh complete imported-closure audit; it preserves, rather than repairs
or hides, inherited cache provenance boundaries.

Read-only verification (no compiler/cache replay):

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_accepted_prefix_partition.py --check-recorded
```

Result: PASS, one green target / five audits / two attempts / one failure.
The auditor checks exact tracked receipts without requiring ignored oleans;
if an olean is present, its exact bytes are checked. Earlier checkpoints and
the concurrent sampler/payment sources were not changed.
