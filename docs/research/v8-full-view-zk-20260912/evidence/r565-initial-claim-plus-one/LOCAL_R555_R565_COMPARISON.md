# Local R555/R565 immutable-input comparison

The following comparisons were made locally with `cmp -s` and `sha256sum`.
All three committed/public inputs are byte-identical:

| Artifact | R555 SHA-256 | R565 SHA-256 | Result |
|---|---|---|---|
| `public.bin` | `2a0e875e8c53d715642afa13d11421d01f3d0fe5fd456b3dceb5fdcaaf2db773` | same | byte-identical |
| `binding.bin` | `24468944da3ee04d13e8150d506679423185efd3f0c1088cb97be2c9be8871d4` | same | byte-identical |
| `transition.bin` | `211db562d22370ed1c2d6fa1e9eef1d3439adf0541a038aa9d905facddfa1444` | same | byte-identical |

The proof bodies are intentionally different because R565 changes the carried
initial wire claim: R555 `proof-1.bin` SHA-256 is
`a67aee246e8da19ba250d1ed517dba0c0b520339be40783cef50298e8471b5c8`;
R565 is `717433b72e6d5427c2908dae26ab5f93ef95b69ee3e00395cc78aad90cea66b7`.

Root comparison used the existing parser layout in the compiled R565 host:
it binds the immutable R555 proof bytes in `prior_proof_bytes`, parses them,
and asserts `prior_wire.roots.0 == a[18][0]` and
`prior_wire.roots.1 == b[18][0]` before the initial claim is changed. The run
then printed the common root bytes:

- C1: `[c9, 32, c1, fe, 55, e1, 4f, 89, b6, 8b, e6, b2, 35, 0e, 7b, 1c, ac, c0, 61, b3, 2f, f6, 16, b0, 67, 3c]`
- C2: `[ea, 09, 38, 27, 0a, 9b, 12, 5f, 3b, 7a, 1b, 84, 68, 1c, 14, 73, 54, ae, 53, dd, 26, 0a, 8a, 1b, 2a, 49]`

This records the retained explicit parser assertion rather than treating a
separate unrecorded parser invocation as evidence.

Read-only NUC checksum of the final release binary:
`bf5292055fab14984fd0e3c9b799709b998d76bef028f17c335d154c9e86387c`.
