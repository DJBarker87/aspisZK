# Independent review: OpeningPolynomialView

Reviewed read-only against the Lean source, focused attempt logs, source
manifest, object archive, and existing checksum index. No Lean build was run.

## Statement and proof scope

`polynomial` is the finite sum `Σ i, C (coefficients i) * X ^ i.val` over
`WideExact`, so coefficients are in ascending monomial order. The generic
`coeff_at` states the coefficient at `i.val` is `coefficients i`;
`polynomial_eval` expands evaluation to the corresponding finite power sum;
`polynomial_natDegree_le` has only the explicit premise `0 < n` and bounds the
degree by `n - 1`. The specializations use seven coefficients, yielding the
stated degree bound 6. `TwoRoundComparison.boundary` is exactly coefficient 0
plus coefficient 4, and each specialized boundary theorem follows by applying
`coeff_at` at those two positions. These conclusions match the theorem
statements in the source. The payload-specialized theorems add no premises.

This is a mathematical polynomial view of the typed coefficient payloads. It
does not state that Rust's Horner evaluation refines this polynomial, nor does
it prove protocol acceptance or extraction.

## Evidence integrity

- Final source, successful attempt snapshot, and current Lean source all have
  SHA-256 `23ea3b82a3266da3525784a3976769f6bcec33d6d0a5ee07e63fa5675d233730`.
- Attempt b's receipt records exit 0, 2.31 seconds, 3,569,460 KiB peak RSS,
  zero swap, and cgroup caps 4G/6G/0 with TasksMax 128. Its complete log has
  seven `#print axioms` reports; every report lists only `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
- The manifest's source hashes agree with the archived direct-import
  snapshots. Each of the three `.olean` members extracted from
  `compiled-objects.tar.gz` matches the manifest's hash and size. The archive
  SHA-256 is
  `55f7ffcb88386dd122276555a4964d15697a227806fdcf6f7ba6f3ba190fd58b`.
- `sha256sum -c SHA256SUMS` passed before adding this review. The index is
  refreshed below to include this file.

No discrepancy was found in the reviewed theorem statements or evidence.
