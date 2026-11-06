# NKK component certificates

TX2:124 OPEN; target not yet established. These native component certificates are not composed-row credit. NKK_NATIVE_CERTIFICATES.json is authoritative for domains, source hashes, resource metrics, graph/lock checks and controls.

| Component | Positive | Matched failing controls | Native domain |
|---|---|---|---|
| query_chunk8 | NKK_K003 | NKK_K004 | raw4×8; arbitrary replies/posts; backing1768 |
| query_chunk6 | NKK_K006 | NKK_K007, NKK_K008 | raw4×6; arbitrary replies/posts; backing1768 |
| state_roots_stage | NKK_K009 | NKK_K010, NKK_K011 | raw32×3; full payload/log/frame |
| gamma_stage | NKK_K013 | NKK_K014, NKK_K015 | E×4 thenK; exact Result/error prefix; full cursor/backing |
| z_claim_stage | NKK_K016 | NKK_K017, NKK_K018 | K×4,E×2,K; exact Result/error prefix |
| semantic_writeback_stage | NKK_K025 | NKK_K026, NKK_K027 | full array10/cursor reply plus followingK; complete Err prefix |
| owned_tail_stage | NKK_K022 | NKK_K023, NKK_K024 | SAME owned weights64; cursor guard and actual native Drop site; pinned std/allocator retained |
| header_prefix_stage | NKK_K028 | NKK_K029, NKK_K030 | length/magic/tag/next/flag/reserved; exact any scan prefix |
| proof_digest_frame_contract | NKK_K042 | NKK_K046, NKK_K047 | proof57607; stored32; unconstrained reply32; exact modifies calls/ptr/len; protects full heap outside these fields |
| public_digest_stage | NKK_K034 | NKK_K035 | public0..1880; stored32; reply32; arbitrary public observation incl empty; checkpoint frame |
| checkpoint_digest_stage | NKK_K036 | NKK_K043, NKK_K044 | literal22 + SAME prefix1736; arbitrary entire-prefix observation; reply32 |
| pair_owned_window | NKK_K045 | NKK_K048, NKK_K049 | SAME Prepared+owned Vec64; returned weights/rhs/power/next + allocation frame; Prepared variant only |

All 50 Kani attempts are terminal. Every positive and accepted control resolved the frozen dependency graph offline, with deployed features and an unchanged frozen Cargo.lock. Exact KMX patch SHA is `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.

K032/037–041 calibrate the borrowed-slice/record/Result<Unit,Error> contract shape before K042: inverted ensures fails, an unimplied caller assertion passes on the real body and fails under stub_verified, and modifies violation is detected. Supplementary K050 wrong-argument control fails. The native contract is the owner's existing option-A P6/D188 tool-trust reclassification.

K001/K002 were own missing-input compile failures; K012 exposed an incorrect worker expectation for constructor-normalized E values; K021 was an invalid cancelled wrong-cursor control (PASS), repaired by K025/026/027. K031's 90s byte-selection timeout is retired unchanged. The replacement K042 uses a different checked modifies frame, protecting the complete proof/stored/reply buffers. All original verdicts remain; see NKK_FINDINGS.md.

K045 asserts full weights/rhs/power/next and the returned owner, but only Prepared.variant. It is not a complete final Prepared frame; retained constructor cuts still need their SAME-argument frame chain. No function-pointer/Option<fn>, writable-static, field-multiplication or new runtime-trust credit is used. No extraction or release build was run.

The selected Lean sources each have successful focused receipts and printed top-theorem axioms. Failed elaborations and their diagnostic sorryAx are excluded. NKK_COMBINED_IMPORT imports NKH_COMBINED_IMPORT, NJU_COMBINED_IMPORT, all selected modules and the deployed headline. Audit results and exact resource fields are in NKK_AUDIT.json and per-attempt receipts. Source clauses and phase joins are not a complete native parent proof.
