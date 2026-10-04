# R724 shifted null certificate: all-code pullback check

This is a bounded arithmetic check of the saved shifted diagnostic's one
left-null vector.  It asks whether that vector is a functional identity on
every arbitrary code vector `c : Fin 1024 -> M31`, before any fold, query, or
other candidate-space restriction.

The check used the exact saved certificate
[`left-nullspace.tsv`](left-nullspace.tsv), the frozen R16 `Transport::inverse`
source [`r16_basis_transport.rs`](source-pins/r16_basis_transport.rs), and the
frozen fixed `ORDER`/`INACTIVE` table
[`r17_basis_tables.rs`](source-pins/r17_basis_tables.rs).  The selected
`v6_statement_points` excerpt fixes the shifted diagnostic's point 0 and
point 2.  For each code basis vector `c=e_j`, it evaluates:

```
lambda_active[j]
  + point0_weight · Transport.inverse(e_j)
  + 715827882 * point2_weight · Transport.inverse(e_j)  (mod 2147483647).
```

The calculation is base-M31 only: the saved certificate and the shifted
points have zero non-base QM31 limbs, so the source transport and multilinear
products remain in that component.  The script directly implements the
inverse's pivot correction and the `WeightAccumulator.add_multilinear`
bit order (coordinate 0 is code bit 9).  It checks all 1,024 basis vectors.

Result: **111 nonzero residual coefficients**.  The certificate therefore is
not a functional identity for arbitrary 1,024-code vectors.  Its residual
support is exactly recorded in
[`all-code-pullback-result.json`](all-code-pullback-result.json):

- `194, 196, …, 224`, then every index `225..255`;
- every index `480..511`;
- every index `736..767`.

Of those, 44 retain a nonzero saved active-chord coefficient and 67 are
point-pullback-only residuals.  The first residual is code index 194 with
value `1910217432`; its two point pullbacks are both zero and its inverse
support is source row 540.

This invalidates only the proposed unrestricted functional-identity reading
of the saved restricted-matrix null vector.  It does not establish a privacy
property, a verifier defect, a rank statement for any constrained space, or a
source-to-model correspondence claim.

## Exact inputs and receipt

The deterministic local command was:

```
python3 check_all_code_pullback.py
```

It exited 0 and wrote `all-code-pullback-result.json`.

| Artifact | SHA-256 |
| --- | --- |
| `check_all_code_pullback.py` | `a2d30b31462d6f0a338b038d6addfb238da134a520bb1b1524a813d6353ab3ff` |
| `all-code-pullback-result.json` | `f217aaeacfd7ae4d8177ca585ff0342dac8b3fef34dfe8a641e7e96a21266aa4` |
| saved null vector | `a17fb74f6312b4ee065c5534dab5404840025804e27c55491d4f049ce3f35068` |
| frozen R16 transport source | `678c64e08e7d14bb6bc160042f0ee01cb39e260748ec1ac95cce008969d586ae` |
| frozen fixed order/inactive table | `c64dd229d516a07a3aad8811bc8fdb7cb393b669952cdfb661da67560867c443` |
| frozen full `v6_transcript.rs` | `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf` |

The old restricted matrix receipt remains
[`manifest.json`](manifest.json): it records the 222-by-241 diagnostic,
rank 221, and one left-null vector.  That receipt did not claim an arbitrary
code-vector identity.
