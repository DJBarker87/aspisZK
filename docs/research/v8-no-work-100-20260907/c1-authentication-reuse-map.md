# Acceptance, authenticated C1, and recovery: reuse frontier

Read-only source audit at research commit
`2a49280b70f17a4539927d7c6fd3121c417f2d7e`. Borrowed V7 pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No Lean source was changed or compiled; this is an obligation map, not a new
kernel result or an imported-artifact audit.

## Strongest reusable result

The relevant early-C1 authentication alternative already exists in V8:
[`AuthenticatedEarlyC1Targets.accepted_opening_prefix_or_shared_failure`](experiments/AuthenticatedEarlyC1Targets.lean).
For any one opening, it derives exact raw-leaf-and-salt projection of the
prefix-fixed C1 word, or a single whole-domain later-target-hit event, or a
shared raw-log truncated-digest collision. It requires accepted path folding,
actual path-call coverage, prefix inclusion, and consistent prefix answers.
It does not require a q16-specific opening collection.

The strongest inspected V7 operational specialization is
[`V7Tag73K13PreQ16ViewAgreement.exact_accepted_openings_yield_preQ16_projections_or_counted_failure`](../../../AspisFormal/AspisFormal/K1/V7Tag73K13PreQ16ViewAgreement.lean).
Its exact runtime record split derives prefix agreement and inclusion, but
`accepted_two_tree_openings` and `ExactPrefixK12SuppliedCoverage` remain inputs.
Its word is fixed before q16, not necessarily before lambda/chi. Reusing that
cutoff unchanged would be too late for the V8 early-C1 argument.

## Obligation map

| Stage | Existing theorem or source | What remains for the selected V8 execution |
|---|---|---|
| Fix the early raw word | `AuthenticatedEarlyC1Prefix.prefixWords`, `fixedC1`, `fixedEarlyC1`, `prefixWords_eq_actual_view`; V7 `V7MerklePrefixTargetCongruence.extractPrefixFixedWords_eq_of_agree_on_log` | Identify the actual root and shared first-answer prefix before lambda/chi. The word may be incomplete/noncanonical; prefix-only totalization is intentional. |
| Obtain authenticated paths | V7 `V7MerkleFirstUnresolvedBinding.acceptedC1Opening_yields_authenticatingPath`; Rust `verify_two_minimal_subtrees_v7_bytes` | Derive each 18-sibling path and all its actual hash calls from successful minimal-multiproof execution, with the original q22 record/query permutation. |
| Project authenticated bytes | `AuthenticatedEarlyC1Targets.accepted_opening_prefix_or_shared_failure`; underlying V7 `V7MerkleAcceptedOpeningProjection.c1_covered_opening_is_projection_or_raw_collision` | Supply the source-derived accepted paths, coverage, consistent answers and prefix inclusion. Use one shared failure event for all openings. |
| Transfer decoded queried symbols | `AuthenticatedEarlyC1Projection.projected_canonical_fibre_matches`; V7 `V7Tag73K13PreQ16QueryHandoff.projected_opening_lane_value_eq`, `query_consistent_of_shared_projected_opening` | Carry strict canonical parsing and exact query positions. V8 uses the normalized quotient, not V7's raw gamma batch; preserve the same four symbols, denominator conditions, alpha and adaptive final. |
| Identify a high-support C1 candidate | `AuthenticatedEarlyC1Projection.authenticated_support_identifies_or_bad`; `EarlyC1LateProjection.late_projection_identifies` | Supply a common support of at least 245609 fibres for the same candidate. Neither theorem derives this support from 22 accepted queries. |
| Recover semantic columns | `EarlyC1GaoRecovery.early_failure_reduction`, `failure_requires_129`; V7 `V7C1SubfieldRecovery.extracted_c1_components_are_base` | Construct authenticated access to the same fixed word, the private 513-fibre sampling experiment and actual encoder/evaluation bindings; then connect recovered columns to the payment constraints. |

The V7 `V7C1ConcreteProjectionBinding.exactInitialEncoder_overlap_cap` and
`V7C1SubfieldRecovery.message_fixed_by_base_projection_of_large_shared_support`
support the base-field descent. They consume actual encoder/support premises;
they are not source FFT refinement or acceptance theorems.

## Smallest useful next deterministic theorem

Proposed target, not yet formalized:
`verify_two_minimal_subtrees_success_supplies_opening_paths`.
It should be generic in the query count; specialize only afterward to q22 and
depth 18.

The inputs are the literal binary verifier's roots, sorted leaf digests,
frontier bytes and a hash-call execution trace. Its conclusion, on success,
constructs for every input leaf an ordered sibling list of the requested
depth, proves `foldPath` equals the corresponding root, and proves each
internal-node call in `openingInputTrace` occurred in that same execution.
Leaf-call coverage belongs to the small calling-loop composition, since the
minimal-multiproof function receives already-hashed leaves.

The proof needs an explicit level invariant: each current node carries paths
for its original descendants. The paired-child case appends the other
current digest; the frontier case appends the actual consumed 26-byte digest.
Both cases respect the low position bit and shift the position right. The
terminal checks establish the root, full depth and exact frontier exhaustion.
This constructs coverage; assuming a supplied coverage predicate would not
close the gap.

The immediate calling-loop adapter must additionally establish:

1. Record ordinal `i` is paired with `queries[i]`; sorting authentication
   entries preserves a bijection back to those original ordinals.
2. The authenticated C1 leaf is exactly bytes `[0,403)` with the shared salt
   `[589,621)` from the same 621-byte record; C2 occupies `[403,589)`.
3. Success carries strict packed-field decoding, rather than accepting the
   totalized `getD 0` value as a parsing certificate.
4. Every leaf and internal-node call belongs to the same shared oracle log,
   and the actual early prefix agrees with its first answers and is included
   in that log.

Then the existing V8 projection theorem yields all q22 C1 projections outside
the two shared Merkle failures. Quantifying the per-opening result is trivial;
the source loop/path/trace invariant is the substantive missing adapter.
Pin the selected build configuration too: `auth_order::entries` and the
gamma-wrapper variants need their exact input/output correspondence. The
host-only differential assertions and `early_c1_trace` honest control are
evidence for those executions, not a universal SBF refinement theorem.
No new assumption-only Lean wrapper was added in this audit.

## Causal and quantitative boundaries

The inspected source order in [`relation_callback.rs`](experiments/relation_callback.rs)
is C1 root, lambda/chi, C2 root, sequential OOD points/answers and later
challenges, then the final word before q22/rho. Authentication must project to
the C1 word fixed at the first cutoff, while allowing C2, candidate selection
and the post-alpha final to remain adaptive at their actual later cutoffs.
The returned proof's record bytes may be disclosed later; their early-word
projection is a conclusion outside the shared failure event, not an imposed
early choice of those bytes.

`AuthenticatedEarlyC1Targets.allTargets_card_le` bounds targets for all
262144 early C1 positions. `EarlyC1OracleGame.game_event_implies_new_target_event`
and `game_probability_le_exact_count` already connect the whole-domain hit to
the finite lazy-oracle model. For positive tape length their rational bound
is `Q * 262144 / 2^208 = Q / 2^190`, with the theorem retaining its explicit
zero-step convention. This is not yet an actual Rust/Fiat–Shamir coupling.
Repeated inputs must use their cached full 256-bit answers; prequeries and
later adversary/verifier calls must be included in the same modeled cache,
and the fresh-call budget must cover the actual execution. The collision
event remains a separate shared charge, not 22 independent charges.

Authentication does not promote a compact batched relation check to every
pointwise query equality; the existing algebraic/batching exceptional events
must remain when transferring acceptance to the query game. Nor can the
V7 q16/641-field parsed-proof interface replace V8's q22/697-field interface
by changing a numeral: `ExactOpeningPositionsSourceBinding` and
`ExactParsedProofSourceBinding` are supplied data equalities in the V7 handoff.
`V7Tag73ExactSourceAcceptanceModel.RootHasStrictSourceRefinement` explicitly
keeps its source/projection identification as a boundary.

## False shortcuts and recovery separation

- [`raw-c1-review.md`](raw-c1-review.md) records an accepted same-execution
  control with two unqueried malformed committed C1 fibres. Thus acceptance
  does not imply globally canonical C1 or a globally exact raw codeword.
  Queried malformed entries still fail strict parsing.
- `V7MerkleAcceptedExtractionClosure.extractV7Words_succeeds_of_complete_graph_and_covered_paths`
  assumes complete graph extraction succeeded. The similarly named
  `V7MerkleQueryExtractor.accepted_two_tree_openings_extract_or_typed_failure`
  retains every typed failure and does not use its acceptance hypothesis to
  eliminate them. Neither supplies global extractability from acceptance.
- Twenty-two four-symbol fibres are not the 245609-fibre support premise,
  nor the 513 private authenticated samples used by Gao recovery. The latter
  theorem gives a bad-set cap of 16535 and failure implies at least 129 bad
  sampled fibres, conditional on the same early object and evaluation setup.
- `SelectedEarlyC1Outputs` supplies later output/alias consequences under its
  candidate and semantic premises; it does not establish those premises from
  source acceptance or replace the authentication/recovery chain.

## Source pins and verification scope

The inspected current V7 sources below matched their borrowed-commit blobs:

| File | SHA256 |
|---|---|
| `K1/V7Tag73K13PreQ16ViewAgreement.lean` | `8708b693f38961c85f67735c34e25878892e229b5078d9af42450372bcfc6565` |
| `K1/V7Tag73K13PreQ16QueryHandoff.lean` | `066b6df06b5dd93ec7a81269720850211c3db1dcc52fa3e0b12eb858b0ed9275` |
| `Pool/V7MerkleFirstUnresolvedBinding.lean` | `5cc1eb37267545da85f5c33dd51a24c698d89ccf5d2a9c4d9290f3593618ccea` |
| `crates/aspis-core/src/v7_merkle208.rs` | `071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf` |

Current V8 source pins: `AuthenticatedEarlyC1Targets.lean`
`317b2deb64edf2e9991d2ab2e4bb3d22706f6ca1fa4106b72703a5a70ce51432`;
`relation_callback.rs`
`285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed`.
Existing proof status is reused from its retained evidence, not replayed here.
No new source-to-Rust, oracle-law, full closure or recovery claim is made.
