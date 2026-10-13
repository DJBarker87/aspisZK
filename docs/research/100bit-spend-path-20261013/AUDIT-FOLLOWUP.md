# Follow-up to the runtime and soundness audit

2026-10-13. The full transparent private-spend security goal remains open.
The following separates measured results from source arguments and theorem
obligations.

| Audit item | Current evidence | Remaining limitation |
|---|---|---|
| P2-to-first-stage CU gap | `P2-CU-RECONCILIATION.md` and `validate_p2_cu.py` reconstruct every phase from four raw marker streams. First-stage savings are 679,500 / 893,354 CU. P2-to-final-D18 savings are 1,109,841 / 1,129,503 CU. | The earlier approximate 1.1M-per-tx description conflated the first and final optimization stages. |
| Removed tx2 strict field scan | `AUTHENTICATED-PARSER-AUDIT.md` covers every arithmetic encoding and every account writer. Tx1 scans all 22 records, then its checkpoint binds the exact proof and public bytes. | The checksum is unkeyed; authentic checkpoint provenance, trusted deployment history and hash binding are required. This is a source audit, not compiled source correspondence. |
| Random full masks | P3 fresh-OS full masks pass transfer and withdrawal at 13, 255 and 1,023 populated pairs. The same transfer statement has three independent OS draws and a deterministic full-mask control. | CU varies: 284 CU in tx1 and 171 CU in tx2 across those four cases. Observed headroom is positive, but there is no uniform cost bound over all inputs. |
| Actual-field privacy | The fresh salted P3 proof passes the actual-challenge rank gate: 16 C1 ranks 112, H1 rank 94/95, silent rank 1076, pure image rank 1080, all 29 two-pad identities. | Finite rank evidence does not prove an efficient simulator, universal rank/density, publication/abort behavior or the ROM hybrid. |
| Soundness | `ConcreteBinding.binding` now composes actual stored-domain geometry, both fold restorations, extraction into the literal 100-entry joint list, both round comparisons and six per-lane functional claims. | The field-level query/rho connection and independent-answer sampler bounds now also compile; see `QUERY-BINDING.md`. Actual Rust functional/verifier correspondence, semantic composition, shared-oracle Fiat--Shamir and zero knowledge remain open. |

P3 is a separate default-off research profile. It adds 32-byte private salts
to all three committed trees, a reserved OS-attempt API, and separate proof,
transcript, profile and release domains. It remains labelled UNPROVED.
The source/artifact/run reconciliation is in
`evidence/p3-private-leaf-salts-20261013/provenance-validation.json`.
No live deployment or fund movement was performed; task keys remain on the NUC.

The proposed soundness ledger still has an approximately 105.136-bit
per-oracle-query coefficient. A final theorem must retain the actual query
count and hash/oracle collision terms. No work or grinding factor is credited,
and no absolute 100-bit claim is made while these obligations remain open.
