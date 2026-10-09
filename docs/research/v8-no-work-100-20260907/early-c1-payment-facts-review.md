# One-copy-branch early-C1 payment facts

Status: both focused leaves are kernel-checked on the capped Tailscale NUC.

- [SelectedEarlyC1PaymentFacts.lean](experiments/SelectedEarlyC1PaymentFacts.lean)
- [SelectedEarlyC1PaymentAssetBound.lean](experiments/SelectedEarlyC1PaymentAssetBound.lean)

## Exact deterministic endpoint

`transfer_facts_of_aliases` takes one actual `WeightedAliases` result for one
fixed early-C1 table.  In that one alias branch it derives, in dependency
order:

1. strict decoded input/output/change amounts and conservation;
2. owner-key, input-note and public-nullifier hash facts;
3. the decoded occupied input pair, spendable selected slot and all 24
   parsed direction bits;
4. two positive output-note openings and their public commitments.

All four results refer to the same `semanticTable candidate`.  Output
positivity and conservation consume the amount result proved in step 1;
they are not independently assumed.

`member_transfer_facts_or_copy_collision` calls the existing selected
`source_member_covered` theorem once.  Its conclusion is therefore one joint
`TransferFacts` value or the one existing `(lambda,chi)` copy-collision
event.  It does not union four separately selected candidates or charge the
same collision four times.

`early_transfer_facts_or_copy_collision` replaces assumed family membership
with the checked `earlyC1 c1 = some candidate` interface and the new strong
support-to-family theorem.  The candidate is fixed from C1 before
lambda/chi, C2, gamma, and every final-selection challenge.

The separate asset-bound leaf supplies `liftBase publicAsset` to the
positive-pack check while using that same `publicAsset` for the input and
both output notes.  This prevents a generic extension-field positive-pack
parameter from being confused with the caller's payment asset.  The caller
authentication of that public asset remains an outer context obligation.

## Premises still visible

This is not yet an accepted-verifier-to-witness theorem.  The following are
explicit premises, not conclusions hidden behind `TransferFacts`:

- the amount, note-hash, occupied-pair and output semantic residuals;
- the selected copy/helper conditions and their non-pole boundaries;
- the public asset, nullifier and two output-commitment cell bindings;
- the positive-pack result and canonical base-valued C1 word.

The next source bridge must show that corrected V8 semantic acceptance
enforces precisely these residuals on this same recovered table, outside
named algebraic collision events.  Relevant reusable V7 work is
`V7AcceptedSemanticRelationComposition.constraint_rows_vanish_of_compact_acceptance`
and `V7AtomicSemanticRowsFromTrace`; their trace columns and selected V8
masked/copy layout must be matched rather than assumed identical.

Even after those premises are derived, the outer membership-path/root,
authoritative caller/account context, nullifier availability, exact account
transition, and atomic settlement validator must be assembled into a checked
transfer witness.  Mathematical family existence is not an executable
replay extractor.

No verifier message or proof value changes.  The body remains 40,282 bytes.
These are deterministic extraction/source bridges, not CU measurements,
Fiat--Shamir bounds, or full-view ZK results.

## Focused verification

`SelectedEarlyC1PaymentFacts` v1 failed only because its direct input-note
module was not imported; the resulting unknown-name errors are diagnostic.
V2 added that existing import and passed all three audits.  A later attempt
to alter the already frozen green target was correctly refused by the NUC
state guard before Lean ran; the refinement was instead placed in a new
dependent asset-bound leaf.

The asset-bound leaf v1 lacked the namespace exposing `liftBase`.  V2 opened
the already imported `PositivePackBinding` namespace and passed its audit.

| Target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps |
| --- | --- | ---: | ---: | ---: | ---: |
| PaymentFacts | v1 | 1 | 2.68 | 6,681,384 | 0 |
| PaymentFacts | v2 | 0 | 2.80 | 6,716,108 | 0 |
| AssetBound | v1 | 1 | 2.70 | 6,679,620 | 0 |
| AssetBound | v2 | 0 | 2.90 | 6,710,592 | 0 |

Lean 4.32.0 ran with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPUQuota 200%.  PaymentFacts v2 passed 1,001 provenance
entries before and after; AssetBound v2 passed 1,003.  Both record
`PROVENANCE_UNCHANGED=true`; neither rebuilt dependencies or packages.  The
green declarations use only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx` or new axiom.

Transport used Tailscale numeric IP `100.108.41.90`; `nuc.local` was only
the pinned SSH host-key alias.  The inherited cache pins research revision
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 revision
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

| Artifact | SHA-256 |
| --- | --- |
| PaymentFacts green source / v2 snapshot | `98ff65e8dc61a3108108b9e289173c62bda97d32b0de55129b5e887a4ee49da6` |
| PaymentFacts green olean | `1164dd2076b886c55883189384f22f2534d1cb44795ff508b2f22fa093b50096` |
| PaymentFacts v2 manifest | `95490c9a250e795a0322eb311baa3831de5a3a6541bb3f311106a666c11307a1` |
| PaymentFacts v2 log | `8ad9beb891733c10a9c4f5c61eeb59080c68e95073acbabeda60ed0a39710e71` |
| AssetBound green source / v2 snapshot | `c74a207bab59571f2dcdcc58370dc770b90792e3a2425d34789caef57dfaf8a1` |
| AssetBound green olean | `9158641b64a498d26257d56fbfe8cfcfd69e85351eca3dae9eb8bc8645c1aada` |
| AssetBound v2 manifest | `4161a51d97d98b4d5f1b9e310c238a107397bc2fbdd26e1a5ecd98fc490d4bdb` |
| AssetBound v2 log | `1a2841f37673c30b53603d85b613b772fe649a7db74e26530a2638f9ff5fbe0a` |

All actual Lean attempts retain their exact source snapshot, manifest and
log under `experiments/selected-early-c1-payment-{facts,asset-bound}-nuc-vN`.
