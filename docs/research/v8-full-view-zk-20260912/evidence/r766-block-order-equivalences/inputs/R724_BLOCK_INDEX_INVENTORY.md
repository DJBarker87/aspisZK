# R724 block index metadata inventory

Certificate: `/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922/.r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json` (SHA-256 `d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4`); the published R747 copy has the same SHA-256.
Raw matrix: `/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922/.r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/matrix.raw.tsv` (SHA-256 `91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af`), matching the certificate’s `input_matrix_sha256_expected`.

The certificate contains 41 SCC blocks whose dimensions sum to 222. For every block, its `vertices` are positions in the 222×222 minor; the metadata satisfies `rows_original[k] = row_origin_order[vertices[k]]` and `columns_original[k] = selected_columns[vertices[k]]`. Inverting `row_origin_order` and the selected-column lookup maps these original IDs back to the same minor positions as `vertices`.

| SCC | Flat interval | Dimension |
|---:|:---:|---:|
| 0 | [0, 6) | 6 |
| 1 | [6, 7) | 1 |
| 2 | [7, 10) | 3 |
| 3 | [10, 18) | 8 |
| 4 | [18, 34) | 16 |
| 5 | [34, 35) | 1 |
| 6 | [35, 74) | 39 |
| 7 | [74, 76) | 2 |
| 8 | [76, 84) | 8 |
| 9 | [84, 100) | 16 |
| 10 | [100, 101) | 1 |
| 11 | [101, 105) | 4 |
| 12 | [105, 121) | 16 |
| 13 | [121, 125) | 4 |
| 14 | [125, 126) | 1 |
| 15 | [126, 130) | 4 |
| 16 | [130, 132) | 2 |
| 17 | [132, 133) | 1 |
| 18 | [133, 135) | 2 |
| 19 | [135, 139) | 4 |
| 20 | [139, 141) | 2 |
| 21 | [141, 142) | 1 |
| 22 | [142, 150) | 8 |
| 23 | [150, 152) | 2 |
| 24 | [152, 154) | 2 |
| 25 | [154, 156) | 2 |
| 26 | [156, 157) | 1 |
| 27 | [157, 161) | 4 |
| 28 | [161, 163) | 2 |
| 29 | [163, 164) | 1 |
| 30 | [164, 166) | 2 |
| 31 | [166, 168) | 2 |
| 32 | [168, 176) | 8 |
| 33 | [176, 184) | 8 |
| 34 | [184, 188) | 4 |
| 35 | [188, 190) | 2 |
| 36 | [190, 193) | 3 |
| 37 | [193, 197) | 4 |
| 38 | [197, 205) | 8 |
| 39 | [205, 221) | 16 |
| 40 | [221, 222) | 1 |

Index-only validation confirms the flattened vertex sequence is a permutation of `Fin 222`; flattened original row IDs are `0..221`; and mapping flattened raw columns through `selected_columns⁻¹` gives a permutation of `Fin 222`. The exact block arrays, flat permutations, inverse arrays, and offsets are in `index_inventory.json` (SHA-256 `268e05932211ba21ebdb9d774a58e53f38ed21ef42dc417da8b6d866b175a48e`; builder SHA-256 `6c83b39b8e3fbf3448d299117a4fa734a7d4465d388e486e962cf7eb59a21cfa`).

The field `lower_block_zero_entries_checked` contains the producer-supplied value **23,068**. This inventory copies that claim only; it did not inspect matrix entries or rerun a lower-block zero check. No Lean theorem proving the 23,068 zero entries is included here.

## Suggested Fin 222 interface

Define `blockVertexOrder : Fin 222 → Fin 222` from the concatenated `vertices`; its bijectivity follows from the validated permutation array. Define `blockRowOrder := rowOriginOrder ∘ blockVertexOrder`, a bijection `Fin 222 ≃ Fin 222`. For columns, use the raw original ID array `selectedColumns ∘ blockVertexOrder`, then map through `selectedColumnsRangeEquiv.symm`, where `selectedColumnsRangeEquiv : Fin 222 ≃ Set.range selectedColumns`; this inverse is used only on the selected-column image, not on all of `Fin 242`. The resulting `blockColumnMinorOrder : Fin 222 ≃ Fin 222` is the same vertex permutation. A Lean bridge can state `rowOriginOrder⁻¹ (blockRowOrder i) = blockVertexOrder i` and `selectedColumnsRangeEquiv.symm ⟨blockColumnRawOrder i, proof_raw_is_selected⟩ = blockVertexOrder i`, with inverses represented by the saved inverse arrays.

This is an index/certificate-metadata audit only; it proves no matrix identity, block inverse, determinant, or global rank fact.
