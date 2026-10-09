# Common nodal support to the same early-C1 family member

Status: kernel-checked as one focused leaf on the capped Tailscale NUC.
Source: [NestedMiddleC1Support.lean](experiments/NestedMiddleC1Support.lean).

## Exact new bridge

Fix the same 29 gamma nodes and the same reconstructed originals produced by
the four-alpha middle extractor. Suppose one set `S` of original-code symbol
positions has the literal equality

    rawBatch(c1,c2,gamma,i)
      = exactInitialEncoder(recoveredOriginal(gamma))(i)

for every gamma node and every `i` in `S`.

`common_nodes_subset_own` proves that `S` is contained in the component
tuple's **own** joint agreement set. At a fixed position, the literal symbol
error is a polynomial of degree at most 28 in gamma. Its 29 nodal values are
zero after rewriting with the already-checked nodal reconstruction equality.
The polynomial is therefore zero, and its 29 coefficients give the required
componentwise source/encoder equalities.

If `S.card >= 38228`, `early_member_of_common_nodes` uses the actual 26+3
source projection to prove that the first 26 reconstructed messages belong
to `EarlyC1Family.family e.c1`. `early_member_and_claims` combines this for
the **same reconstructed tuple** with the previous source-shaped proof of all
87 exact point claims.

No candidate membership, received polynomiality or same-support recovery is
assumed. The quotient at every gamma remains reconstructed from four
alpha-adaptive final vectors, and the component tuple remains reconstructed
from the 29 actual originals.

## Remaining soundness seam

The common set is a premise, not an inferred consequence of separate
per-gamma support sizes. This is necessary: the retained block-support
counterexamples give 29 separate middle-support responses whose interpolated
tuple has zero own support. Hence the missing acceptance/extractor theorem
must produce one common authenticated set, or establish a different
quantitative event that supplies early C1.

Family membership plus 87 exact point claims is still not payment validity.
The zero-table countermodel satisfies both while failing strict positive
amount. The next deterministic endpoint must additionally receive the
literal semantic/copy/note/path/output residuals enforced by the selected
terminal, and the probabilistic/source theorem must explain why accepted
forks enforce those residuals on this same table.

This leaf adds no verifier message, proof byte or challenge. The body census
remains 40,282 bytes. It is analysis/extractor logic and has no verifier CU
claim.

## Reused proof chain

| Existing result | Use |
| --- | --- |
| `NestedMiddleClaimExtraction.recovered_components_at_nodes` | Identifies each reconstructed component batch with that gamma's reconstructed original. |
| `TupleQueryTransport.symbolError_eval` | Rewrites the literal 26+3 symbol error as received batch minus encoded reconstructed batch. |
| `OwnSymbolCollision.residual_degree` / `residual_zero_iff` | Supplies degree 28 and reads componentwise equalities from a zero polynomial. |
| `Gamma29Reconstruction.degree28_zero_of_29_nodes` | Turns the 29 distinct nodal zeros into polynomial identity. |
| `SelectedOwnSymbol.own_eq_joint` | Uses the selected original-code joint support, not a V7 raw-word substitute. |
| `SelectedOwnSymbol.own_supported_early_member` | Projects the same tuple into the fixed pre-lambda early-C1 family at 38,228 symbols. |
| `NestedMiddleClaimExtraction.recovered_component_claims_exact` | Adds the 87 actual component claim equations for the same tuple. |

## Focused verification

Only `NestedMiddleC1Support.lean` was compiled. V1 exposed one ambiguous
`own` namespace; v2/v3 exposed a definitional mismatch between the field's
decidable equality and a local classical filter. V4 uses the already-proved
`SelectedOwnSymbol.own_eq_joint` extensional equality instead of unfolding a
Finset with a different decider. No theorem premise, resource limit or import
closure changed.

V4 exited 0 in 2.95 seconds with peak RSS 6,869,624 KiB and zero swaps. All
three declarations audit only to `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorryAx` or new axiom. Lean 4.32.0 ran with
`-j1 -M9500` under MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0 and
CPUQuota 200%. Both 985-entry provenance checks passed with
`PROVENANCE_UNCHANGED=true`; no dependency or package replay ran.

Transport used `dombarker@100.108.41.90` over Tailscale; `nuc.local` was
only the pinned host-key alias. The runner retains research-cache pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; the per-run manifest pins the
exact leaf and imported blobs.

| Artifact | SHA-256 |
| --- | --- |
| Source / exact v4 source snapshot | `663a6156ab0a59830d45863701ea72041e6245d0b6de0ce40c28f909304c8f0a` |
| Green olean | `dbdd26ad9449e633c8e47758d79ae6f4803f5485a1a5e2f99384a084f4e8e80b` |
| Per-run manifest | `e5ca43b5c3cfbaf9fa3811f91547779810b9d4c0765a1e51fdead12cc5bb6620` |
| Log | `9ef09236187d410589a4dd60d8c94be01444f0300d68df9f71d45a4e93ee8dee` |
