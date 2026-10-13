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
| Soundness | `ConcreteBinding.binding` composes stored-domain geometry, both fold restorations, literal joint-list extraction, both round comparisons and six per-lane claims. `MaskedSemantic.large_matching_extracts` now connects the recovered candidate to the old masked semantic/input-note relation, with explicit exclusions. | The field-level query/rho connection and independent-answer sampler bounds also compile; see `QUERY-BINDING.md`. Actual Rust correspondence, new-transcript exclusions and probability accounting, shared-oracle Fiat--Shamir and zero knowledge remain open. |

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

The later sampler/transport checkpoint (`SAMPLER-TRANSPORT.md`) derives the
optimized sampler's intended modulo laws at the Nat/list level, composes D18
tensor weights with the explicit Boolean row functional, and proves the
two-pad determinant/cancellation in a rootless quadratic extension. These
strengthen components of the argument; the source, semantic, Fiat--Shamir
and full privacy obligations listed above remain open.

The next reuse checkpoint (`LEAN-REUSE.md`) derives field typing for every
literal R1 candidate using the unchanged historical descent proofs, connects
the D18 point rows to the original named R0 weights, and derives the
point/extra/codeword-typing witness interface. The UInt64/UInt32 sampler pass
also matches the Nat division model. These are checked component bridges;
the protocol-level semantic, source, shared-oracle and privacy conclusions
remain open.

The subsequent `MASKED-SEMANTIC-BRIDGE.md` checkpoint applies the old masked
semantic theorems to the literal R1 candidate after deriving its point/Libra
claims and base typing. It proves the conditional production/copy/input-note
conclusion. The new transcript must still justify its six semantic exclusion
families with correct prefix timing; source and full settlement/privacy
claims do not follow from the deterministic implication. The combined Lean
import and six axiom audits pass with standard axioms only. The same
checkpoint composes the existing extracted four-byte decoder with the
eight-word machine division pass; full mutable/repeated sampler refinement
is still open.

`SEMANTIC-PREFIX-BRIDGE.md` now derives the candidate exclusions from the
explicit classifier at each of the first 25 parsed semantic rows. The proof
reuses the pre-C2 padding argument for lambda/chi and proves equality of the
R1/R0 candidate predicates. The independent-answer per-prefix budgets sum
to `303100 * (1+deltaQ)/P^4`; the new shared-oracle success bound, Rust
correspondence, full settlement extraction, and privacy remain open. The
combined prefix checkpoint and seven axiom audits pass on the NUC.
