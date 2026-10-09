# Nested higher-Y middle extraction through component claims

Status: kernel-checked as one focused leaf on the capped Tailscale NUC.
Source: [NestedMiddleClaimExtraction.lean](experiments/NestedMiddleClaimExtraction.lean).

## New deterministic endpoint

This leaf composes three previously separate results against one actual
`CausalCoveredRecovery.Execution`:

1. Four distinct alpha-node finals satisfying the actual higher-Y
   `MiddleWitness` predicate reconstruct the canonical natural-1024 quotient
   at that gamma.
2. Applying the literal `ComponentRows.original (atGamma data gamma)` map to
   those reconstructed quotients gives 29 actual original-message responses;
   29 distinct gamma nodes reconstruct a 29-component message tuple.
3. `MiddleWitness` already contains `not badAnchor`. Its third disjunct is
   exactly nonzero repaired ordinary-row error. Therefore the witness gate
   itself—not a newly assumed equation—proves each of the three actual
   gamma-batched row equations. Degree-28 interpolation then proves all 87
   component point claims exact for the reconstructed tuple.

The main endpoint is
`recovered_component_claims_exact`. It permits separate kappa and tau
histories at every alpha node and retains the post-alpha adaptive final. The
final vectors, not a supplied quotient, are inputs to the alpha
reconstruction. The gamma reconstruction reuses the pinned V7 released
interpolation constructor.

## What this closes and what it does not

This closes the deterministic row/claim-transport seam in the proposed
29-gamma by four-alpha higher-Y extractor. It removes an otherwise circular
premise that the reconstructed original messages satisfy the desired three
row equations.

It does not prove any of the following:

- that bare verifier acceptance supplies a `MiddleWitness` at every selected
  alpha continuation;
- that 29 forkable gamma nodes and four inner continuations are collected by
  an ideal or Fiat--Shamir extractor;
- that the reconstructed component tuple has common own support, matches
  authenticated early C1 values, or belongs to `EarlyC1Family`;
- that exact point claims imply copy, amount, note, path, output, context or
  settlement residuals;
- that a checked transfer witness exists or is computed within a declared
  resource bound.

The zero-table countermodel remains decisive for the last distinction: zero
components and zero claims satisfy all equations proved here but fail the
strict positive-amount payment condition. Hence this result must feed a
separate semantic-residual enforcement theorem rather than being renamed
payment extraction.

The existing support counterexample also remains visible: several separate
high-support batched messages can interpolate to a tuple with no joint own
support. Claim exactness does not repair that fact. The next deterministic
target is therefore the same-tuple authenticated-C1/support implication; the
next probabilistic target is the bounded nested collector that supplies the
premises used here.

## Reused V7 and V8 results

| Input | Exact use |
| --- | --- |
| `SelectedMiddleFourAlpha.reconstruct_middle_canonical` | Four actual final vectors reconstruct the common quotient at one gamma. |
| `SelectedMiddleUniqueness.canonical_eq` | A selected middle witness identifies that reconstruction with its actual quotient. |
| `GammaComponentGame.reference_rows` | The actual execution row object with replaced reference is definitionally the source `ComponentRows.rows`. |
| `ComponentRows.point_error` | Converts zero repaired row error into the literal scalar-power component equation. |
| `Gamma29Reconstruction.reconstructed_claims_exact` | Reconstructs messages and reads all 87 exact component claims from 29 nodal equations. |
| Pinned V7 `releasedInterpolationComponents` | Underlies the last row without importing a generic BCS multiplier or a new candidate-family premise. |

## Focused verification

Only `NestedMiddleClaimExtraction.lean` was compiled. Attempts v1--v6 exposed
local elaboration issues: the selected QM31 `NeZero 2` instance was made
explicit, then a deeply nested record-update equality was factored through a
small generic subtraction lemma and named equalities. No theorem hypothesis,
heartbeat limit, recursion limit, memory cap or import closure changed.
Attempt v7 exited 0 in 3.30 seconds with peak RSS 6,868,852 KiB and zero
swaps. All five declarations audit only to `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorryAx` or new axiom.

The run used Lean 4.32.0 with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax
10 GiB, MemorySwapMax 0 and CPUQuota 200%. Both 983-entry provenance checks
passed with `PROVENANCE_UNCHANGED=true`; no dependency or package replay ran.
Transport used `dombarker@100.108.41.90` over Tailscale, with `nuc.local`
only as the pinned host-key alias.

The runner retains research-cache pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The per-run manifest pins the
exact source and all imported blobs separately.

| Artifact | SHA-256 |
| --- | --- |
| Source / exact v7 source snapshot | `446a82029ee1f52fad86930a495d657354e64f8d3fa36c4a8921caca81ac72d2` |
| Green olean | `9666a3bafd5b3847122673dfd6f53b689a64463e5ac63c0e9f8d6d9b75954201` |
| Per-run manifest | `bb0a666977208910cd535c8527422f4be5d64700e7d17272f308cc8ea1161f4b` |
| Log | `988dfac31ad7114757b96edd74978bc85019d4a59642c78979fe773852481030` |
